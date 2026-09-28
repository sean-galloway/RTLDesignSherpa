# TASK-006: Enable Kimi from the cloud (key + egress)

> Migrated 2026-09-27 from `vault/Tasks/docs-review/open.md` as **DOCREV-005** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Status:** CLOSED 2026-09-27 -- the owner confirmed the docs-review work is done. No measurement was taken in this session to support that; the basis is Sean's statement, recorded as such rather than presented as verification.
**Status (as filed):** open 2026-07-23 — prerequisite for running any new round off the workstation

The scripts are endpoint-agnostic ([[kimi-review-rounds]]), but two things
outside the repo have to be arranged before a cloud round can run:

- [ ] **Key as a sandbox secret.** `MOONSHOT_API_KEY` lives in
      `/mnt/data/github/seans-cli-ai-local/config/frontier-keys.env`, untracked
      on one disk. Set it in the cloud environment's secret store as
      `KIMI_API_KEY` — pasted into the secret settings, never into a file, never
      committed, never on removable media. Also set
      `KIMI_BASE_URL=https://api.moonshot.ai/v1` and `KIMI_MODEL=kimi-k3`
      (`kimi-k2` is the local proxy alias and 404s against Moonshot directly).
- [ ] **Egress.** Sandboxes filter outbound network; `api.moonshot.ai` may need
      allowlisting. If the first call hangs or 403s, that is the cause — nothing
      in the scripts can work around it.
- [ ] Confirm the model id is accepted. `kimi-k3` is what `litellm-config.yaml`
      routes to, but no live direct call has been made to verify Moonshot takes
      it unprefixed. `GET /v1/models` with the real key lists the valid ids.

**Not a blocker on the workstation.** Direct-mode rounds run fine here (the
reset cdc round is the proof case); this gates only rounds run from a cloud
sandbox.

---
