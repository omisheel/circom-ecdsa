#!/bin/bash

BUILD_DIR=../../build/verify
CIRCUIT_NAME=verify

if [ ! -d "$BUILD_DIR" ]; then
    echo "Creating build directory..."
    mkdir -p "$BUILD_DIR"
fi

echo "****COMPILING CIRCUIT****"
start=`date +%s`
circom "$CIRCUIT_NAME".circom --r1cs --wasm --sym --output "$BUILD_DIR" -l ../../circuits
end=`date +%s`
echo "DONE ($((end-start))s)"

echo ""
echo "****CIRCUIT INFO****"
npx snarkjs r1cs info "$BUILD_DIR"/"$CIRCUIT_NAME".r1cs

echo ""
echo "****GENERATING WITNESS FOR SAMPLE INPUT****"
start=`date +%s`
if ! node "$BUILD_DIR"/"$CIRCUIT_NAME"_js/generate_witness.js "$BUILD_DIR"/"$CIRCUIT_NAME"_js/"$CIRCUIT_NAME".wasm input_verify.json witness.wtns 2>&1; then
    echo ""
    echo "ERROR: Witness generation failed!"
    echo "This typically means the input values don't satisfy circuit constraints."
    echo ""
    echo "For Ed25519, common issues include:"
    echo "- Public key doesn't lie on the Ed25519 curve"
    echo "- Signature values (r, s) are out of range"
    echo "- The signature doesn't verify against the message hash and public key"
    echo ""
    echo "The input file 'input_verify.json' appears to contain secp256k1 values,"
    echo "not Ed25519 values. You need to generate proper Ed25519 test data."
    exit 1
fi
end=`date +%s`
echo "DONE ($((end-start))s)"

echo ""
echo "****CHECKING WITNESS (Verifying constraints)****"
npx snarkjs wtns check "$BUILD_DIR"/"$CIRCUIT_NAME".r1cs witness.wtns

echo ""
echo "****EXPORTING WITNESS TO JSON (to see the result)****"
npx snarkjs wtns export json witness.wtns "$BUILD_DIR"/witness.json

echo ""
echo "****VERIFICATION RESULT****"
# The result signal is at index 1 (after the public inputs)
result=$(cat "$BUILD_DIR"/witness.json | jq '.[1]')
if [ "$result" = '"1"' ]; then
    echo "✓ Signature verification PASSED (result = 1)"
else
    echo "✗ Signature verification FAILED (result = 0)"
fi