## dataint_ecc_hamming_encode_secded -- Formal Proof

The encoder is formally verified as part of the combined encode+decode roundtrip
proof located at:

    formal/common/dataint_ecc_hamming/

That proof instantiates both `dataint_ecc_hamming_encode_secded` and
`dataint_ecc_hamming_decode_secded` and proves:

1. Roundtrip correctness (encode then decode recovers original data)
2. No error flags on clean codewords
3. SECDED parity bit is XOR of all lower bits
4. Reset behavior of decoder outputs

To run:

    cd formal/common/dataint_ecc_hamming
    sby -f ecc_hamming.sby

No separate proof is needed for the encoder alone since the roundtrip proof
exercises all encoder outputs through the decoder.
