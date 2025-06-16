pragma circom 2.0.2;

include "../../circuits/ecdsa.circom";

component main {public [s, R, m, A]} = ed25519SSHVerifyNoPubkeyCheck(64, 4);
