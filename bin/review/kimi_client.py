#!/usr/bin/env python3
"""Transport for Kimi review calls. Works two ways, same code.

    LOCAL   scripts -> litellm proxy on localhost:4000 -> Moonshot
    CLOUD   scripts -> https://api.moonshot.ai/v1 directly

The proxy does not exist in a cloud sandbox, so the endpoint, key and model are
read from the environment instead of being baked in:

    KIMI_BASE_URL   default http://localhost:4000/v1   (local proxy)
    KIMI_API_KEY    default sk-x                       (dummy proxy token)
    KIMI_MODEL      default kimi-k2                    (proxy alias)

For cloud, set all three -- and note that KIMI_MODEL must then be a real
Moonshot model id, not the proxy alias. `kimi-k2` only means something to the
proxy; sending it straight to api.moonshot.ai gets you a 404.

    export KIMI_BASE_URL=https://api.moonshot.ai/v1
    export KIMI_API_KEY=<the real MOONSHOT_API_KEY>
    export KIMI_MODEL=kimi-k2-0711-preview

Budget ladder (this is the expensive lesson, do not remove it): Kimi is a
reasoning model and reasoning tokens are drawn from the completion budget. Ask
for too little and `content` comes back EMPTY with finish_reason=length -- not
an error, just nothing. So every call carries an explicit large max_tokens and
escalates 32768 -> 65536 -> 131072 on an empty body. If a unit still truncates
at 131072, split the unit in the bundler rather than raising the ceiling again.
"""
import json
import os
import time
import urllib.error
import urllib.request

DEFAULT_LADDER = (32768, 65536, 131072)


def config():
    """Resolve endpoint/key/model from the environment."""
    return {
        "base_url": os.environ.get("KIMI_BASE_URL", "http://localhost:4000/v1").rstrip("/"),
        "api_key": os.environ.get("KIMI_API_KEY", "sk-x"),
        "model": os.environ.get("KIMI_MODEL", "kimi-k2"),
    }


def describe():
    """One-line summary of where calls will go, for logs. Never prints the key."""
    c = config()
    where = "local proxy" if "localhost" in c["base_url"] or "127.0.0.1" in c["base_url"] else "direct"
    return f"{c['model']} @ {c['base_url']} ({where})"


def preflight():
    """Fail loudly and early on an obviously-wrong config.

    A cloud run that dies 40 minutes in because the key was never exported has
    burned the whole session. Check before the first unit, not during it.
    """
    c = config()
    problems = []
    if "localhost" not in c["base_url"] and "127.0.0.1" not in c["base_url"]:
        # Direct mode: the dummy proxy token and the proxy alias are both wrong.
        if c["api_key"] in ("", "sk-x"):
            problems.append("KIMI_API_KEY is unset or still the dummy proxy token 'sk-x'")
        if c["model"] == "kimi-k2":
            problems.append("KIMI_MODEL is still the proxy alias 'kimi-k2' -- "
                            "direct mode needs a real Moonshot model id")
    return problems


def _post(payload, timeout):
    c = config()
    req = urllib.request.Request(
        f"{c['base_url']}/chat/completions",
        data=json.dumps(payload).encode(),
        headers={"Content-Type": "application/json",
                 "Authorization": f"Bearer {c['api_key']}"},
    )
    with urllib.request.urlopen(req, timeout=timeout) as r:
        return json.load(r)


def call(brief, user, max_tokens, timeout=3600, net_retries=3):
    """One completion. Returns (text, finish_reason, usage, elapsed_s).

    net_retries covers transient transport failures only (a dropped connection,
    a 5xx). Cloud egress is less reliable than a loopback proxy, so a bare
    urlopen that worked locally will occasionally fail there for reasons that
    have nothing to do with the request.
    """
    c = config()
    payload = {
        "model": c["model"],
        "messages": [{"role": "system", "content": brief},
                     {"role": "user", "content": user}],
        "max_tokens": max_tokens,
    }
    t0 = time.time()
    last = None
    for attempt in range(net_retries):
        try:
            d = _post(payload, timeout)
            ch = d["choices"][0]
            return (ch["message"].get("content") or "",
                    ch.get("finish_reason"),
                    d.get("usage", {}),
                    time.time() - t0)
        except urllib.error.HTTPError as e:
            body = e.read()[:400].decode("utf-8", "replace")
            last = f"HTTP {e.code}: {body}"
            # 4xx is our fault (bad key, bad model, oversized request) -- do not
            # retry it, the next attempt fails identically and wastes minutes.
            if 400 <= e.code < 500:
                raise RuntimeError(last) from None
        except Exception as e:  # noqa: BLE001 - transport is genuinely open-ended
            last = f"{type(e).__name__}: {str(e)[:300]}"
        if attempt < net_retries - 1:
            backoff = 5 * (attempt + 1)
            print(f"      transport retry {attempt + 1}/{net_retries - 1} "
                  f"in {backoff}s ({last})", flush=True)
            time.sleep(backoff)
    raise RuntimeError(last or "unknown transport failure")


def call_with_ladder(brief, user, ladder=DEFAULT_LADDER, timeout=None, log=print):
    # KIMI_TIMEOUT overrides the per-request socket timeout. Large
    # reasoning units need it: the bridge_mas humanize unit (and the DV
    # `shared` unit before it) died on a 1h socket timeout while the
    # model was still legitimately thinking, not on token budget.
    if timeout is None:
        timeout = int(os.environ.get("KIMI_TIMEOUT", "3600"))
    """Escalate the completion budget until we get a COMPLETE body.

    Two distinct under-budget failures, and only one of them is obvious:

      empty  + finish=length   reasoning consumed the whole budget, nothing emitted
      partial + finish=length  the critique was cut off mid-sentence

    The second is the dangerous one -- it looks like a successful unit and gets
    filed as one, so findings that were never emitted read as findings that do
    not exist. Escalate on finish=length regardless of how much came back.

    Returns (text, meta_dict). meta records which budget actually worked so a
    later round can start there instead of re-paying for the failed attempts.
    """
    for i, budget in enumerate(ladder):
        txt, finish, usage, elapsed = call(brief, user, budget, timeout=timeout)

        # A server-side refusal is NOT a budget problem. `engine_overloaded`
        # (HTTP 429) and friends come back with an empty body, which the ladder
        # used to read as "reasoning ate the budget" and answer by asking for
        # MORE tokens -- the one response guaranteed not to help an overloaded
        # engine, and it burns the remaining rungs before failing the unit.
        # Case: cdc_part_02 in qc round_5 escalated 32768 -> 65536 -> 131072 on
        # a 429 and died, losing the unit.
        if finish in ("engine_overloaded", "server_error", "rate_limited"):
            raise RuntimeError(
                f"server refused at {budget} (finish={finish}); this is a transport "
                f"failure, not a budget one. Re-send the unit with --resume rather "
                f"than raising max_tokens.")

        if txt.strip() and finish != "length":
            return txt, {
                "finish_reason": finish,
                "max_tokens": budget,
                "usage": usage,
                "elapsed_s": round(elapsed, 1),
                "content_chars": len(txt),
                "budget_escalations": i,
            }
        if i < len(ladder) - 1:
            why = "empty" if not txt.strip() else f"truncated ({len(txt)} chars)"
            log(f"      {why} at {budget} (finish={finish}) -> retry at {ladder[i + 1]}")
    raise RuntimeError(f"still truncated at every budget up to {ladder[-1]}; "
                       "split this unit in the bundler instead of raising the ceiling")
