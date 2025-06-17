pragma circom 2.0.2;

include "bigint_func.circom";

// 10 registers, 64 bits. registers can be overful
// adds 13 bits to overflow, so don't input overful registers which are > 238 bits
// input registers can also be negative; the overall input can be negative as well
template Ed25519PrimeReduce10Registers() {
    signal input in[10];
    
    signal output out[4];
    var offset = 38; // 6 bits
    var offset2 = 38 * 38; // 11 bits

    out[3] <== (offset * in[7]) + in[3];
    out[2] <== (offset * in[6]) + in[2];
    out[1] <== (offset2 * in[9]) + (offset * in[5]) + in[1];
    out[0] <== (offset2 * in[8]) + (offset * in[4]) + in[0];
}

// 7 registers, 64 bits. registers can be overful
// adds 7 bits to overflow, so don't input overful registers which are > 244 bits
// input registers can also be negative; the overall input can be negative as well
template Ed25519PrimeReduce7Registers() {
    signal input in[7];
    
    signal output out[4];
    var offset = 38; // 6 bits
    
    out[3] <== in[3];
    out[2] <== (offset * in[6]) + in[2];
    out[1] <== (offset * in[5]) + in[1];
    out[0] <== (offset * in[4]) + in[0];
}

// check if in < p
template CheckInRangeEd25519() {
    signal input in[4];
    component lessThan[2];

    //lessThan[0] for in[3] < 2^63
    // lessThan[0] = LessThan(64);
    // lessThan[0].in[0] <== in[3];
    // lessThan[0].in[1] <== (1 << 63);
    // lessThan[0].out === 1;

    //now check is similar to secp256k1
    component range64[4];
    for(var i = 0; i < 4; i++){
        if (i == 3) {
            range64[i] = Num2Bits(63);
        } else {
            range64[i] = Num2Bits(64);
        }
        range64[i].in <== in[i];
    }
    var bitsum = 0;
    for (var i = 0; i < 4; i++) {
        for (var j = ((i == 0) ? 5 : 0); j < ((i == 3) ? 63 : 64); j++) {
            bitsum += range64[i].out[j];
        }
    }
    // bitsum will equal 250 if top 250 bits are all 1
    component allEqual = IsEqual();
    allEqual.in[0] <== bitsum;
    allEqual.in[1] <== 250;

    signal last <== range64[0].out[0] + 2 * range64[0].out[1] + 4 * range64[0].out[2] + 8 * range64[0].out[3] + 16 * range64[0].out[4];
    // check if last < 13
    component lessThanLast = LessThan(5);
    lessThanLast.in[0] <== 13;
    lessThanLast.in[1] <== last;
    // if last >= 13, then the input is not in range
    (1 - lessThanLast.out) * allEqual.out === 0;
}

// 64 bit registers with m-bit overflow
// registers (and overall number) are potentially negative
template Ed25519CheckCubicModPIsZero(m) {
    assert(m < 236); // since we deal with up to m+16 bit, potentially negative registers

    signal input in[10];

    // the ec25519 field size, hardcoded
    signal p[4];
    var p_temp[100] = get_ed25519_prime(64, 4);
    for (var i = 0; i < 4; i++) {
        p[i] <== p_temp[i];
    }

    // now, we compute a positive number congruent to `in` expressible in 4 overflowed registers.
    // for this representation, individual registers are allowed to be negative, but the final number
    // will be nonnegative overall.
    // first, we apply the secp 10-register reduction technique to reduce to 4 registers. this may result
    // in a negative number overall, but preserves congruence mod p.
    // our intermediate result is z = secpReduce(in)
    // second, we add a big multiple of p to z, to ensure that our final result is positive. 
    // since the registers of z are m + 13 bits, its max abs value is 2^(m+13 + 192) + 2^(m+13 + 128) + ...
    // so we add p * 2^(m-49), which is a bit under 2^(m+206) and larger than |z| < 2^(m+43+192) + eps
    signal reduced[4];
    component ed25519Reducer = Ed25519PrimeReduce10Registers();
    for (var i = 0; i < 10; i++) {
        ed25519Reducer.in[i] <== in[i];
    }
    signal multipleOfP[4];
    for (var i = 0; i < 4; i++) {
        multipleOfP[i] <== p[i] * (1 << (m-49)); // m - 49 + 64 = m+15 bits
    }
    for (var i = 0; i < 4; i++) {
        reduced[i] <== ed25519Reducer.out[i] + multipleOfP[i]; // max(m+13, m+15) + 1 = m+16 bits
    }

    // now we compute the quotient q, which serves as a witness. we can do simple bounding to show
    // that the the expected quotient is always expressible in 3 registers (i.e. < 2^192)
    // so long as m < 231
    signal q[3];

    var temp[100] = getProperRepresentation(m + 16, 64, 4, reduced);
    var proper[8];
    for (var i = 0; i < 8; i++) {
        proper[i] = temp[i];
    }

    var qVarTemp[2][100] = long_div(64, 4, 4, proper, p);
    for (var i = 0; i < 3; i++) {
        q[i] <-- qVarTemp[0][i];
    }

    // we need to constrain that q is in proper (3x64) representation
    component qRangeChecks[3];
    for (var i = 0; i < 3; i++) {
        qRangeChecks[i] = Num2Bits(64);
        qRangeChecks[i].in <== q[i];
    }

    // now we compute a representation qpProd = q * p
    signal qpProd[6];
    component qpProdComp = BigMultNoCarry(64, 64, 64, 3, 4);
    for (var i = 0; i < 3; i++) {
        qpProdComp.a[i] <== q[i];
    }
    for (var i = 0; i < 4; i++) {
        qpProdComp.b[i] <== p[i];
    }
    for (var i = 0; i < 6; i++) {
        qpProd[i] <== qpProdComp.out[i]; // 130 bits
    }

    // finally, check that qpProd == reduced
    component zeroCheck = CheckCarryToZero(64, m + 16, 6);
    for (var i = 0; i < 6; i++) {
        if (i < 4) { // reduced only has 4 registers
            zeroCheck.in[i] <== qpProd[i] - reduced[i]; // (m + 16) + 1 bits
        } else {
            zeroCheck.in[i] <== qpProd[i];
        }
    }
}

// 64 bit registers with m-bit overflow
// registers (and overall number) are potentially negative
template Ed25519CheckQuadraticModPIsZero(m) {
    assert(m < 182); // so that we can assume q has 2 registers

    signal input in[7];

    // the ec25519 field size
    signal p[4];
    var p_temp[100] = get_ed25519_prime(64, 4);
    for (var i = 0; i < 4; i++) {
        p[i] <== p_temp[i];
    }

    // now, we compute a positive number congruent to `in` expressible in 4 overflowed registers.
    // for this representation, individual registers are allowed to be negative, but the final number
    // will be nonnegative overall.
    // first, we apply the secp 7-register reduction technique to reduce to 4 registers. this may result
    // in a negative number overall, but preserves congruence mod p.
    // our intermediate result is z = secpReduce(in)
    // second, we add a big multiple of p to z, to ensure that our final result is positive. 
    // since the registers of z are m + 7 bits, its max abs value is 2^(m+7 + 192) + 2^(m+7 + 128) + ...
    // so we add p * 2^(m-55), which is a bit under 2^(m+200) and larger than |z| < 2^(m+7+192) + eps
    signal reduced[4];
    component ed25519Reducer = Ed25519PrimeReduce7Registers();
    for (var i = 0; i < 7; i++) {
        ed25519Reducer.in[i] <== in[i];
    }
    signal multipleOfP[4];
    for (var i = 0; i < 4; i++) {
        multipleOfP[i] <== p[i] * (1 << (m-55)); // m - 55 + 64 = m + 9 bits
    }
    for (var i = 0; i < 4; i++) {
        reduced[i] <== ed25519Reducer.out[i] + multipleOfP[i]; // max(m+7, m+9) + 1 = m+10 bits
    }

    // now we compute the quotient q, which serves as a witness. we can do simple bounding to show
    // that the the expected quotient is always expressible in 2 registers (i.e. < 2^192)
    // so long as m < 182
    signal q[2];

    var temp[100] = getProperRepresentation(m + 10, 64, 4, reduced);
    var proper[8];
    for (var i = 0; i < 8; i++) {
        proper[i] = temp[i];
    }

    var qVarTemp[2][100] = long_div(64, 4, 4, proper, p);
    for (var i = 0; i < 2; i++) {
        q[i] <-- qVarTemp[0][i];
    }

    // we need to constrain that q is in proper (2x64) representation
    component qRangeChecks[2];
    for (var i = 0; i < 2; i++) {
        qRangeChecks[i] = Num2Bits(64);
        qRangeChecks[i].in <== q[i];
    }

    // now we compute a representation qpProd = q * p
    signal qpProd[5];
    component qpProdComp = BigMultNoCarry(64, 64, 64, 2, 4);
    for (var i = 0; i < 2; i++) {
        qpProdComp.a[i] <== q[i];
    }
    for (var i = 0; i < 4; i++) {
        qpProdComp.b[i] <== p[i];
    }
    for (var i = 0; i < 5; i++) {
        qpProd[i] <== qpProdComp.out[i]; // 130 bits
    }

    // finally, check that qpProd == reduced
    component zeroCheck = CheckCarryToZero(64, m + 36, 5);
    for (var i = 0; i < 5; i++) {
        if (i < 4) { // reduced only has 4 registers
            zeroCheck.in[i] <== qpProd[i] - reduced[i]; // (m + 10) + 1 bits
        } else {
            zeroCheck.in[i] <== qpProd[i];
        }
    }
}