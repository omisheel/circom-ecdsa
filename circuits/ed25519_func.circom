pragma circom 2.0.2;

// from https://github.com/ethereum/py_ecc/blob/master/py_ecc/secp256k1/secp256k1.py
function get_ed25519_prime(n, k) {
    assert(n == 64 && k == 4);
    var ret[100];
    if (n == 64 && k == 4) {
        ret[0] = 18446744073709551597;
        ret[1] = 18446744073709551615;
        ret[2] = 18446744073709551615;
        ret[3] = 9223372036854775807;
    }
    return ret;
}

function get_ed25519_order(n, k) {
    assert(n == 64 && k == 4);
    var ret[100];
    if (n == 64 && k == 4) {
        ret[0] = 6346243789798364141;
        ret[1] = 1503914060200516822;
        ret[2] = 0;
        ret[3] = 1152921504606846976;
    }
    return ret;
}

function get_ed25519_a(n, k) {
    assert(n == 64 && k == 4);
    var ret[100];
    if (n == 64 && k == 4) {
        ret[0] = 12297829303526400324;
        ret[1] = 12297829382473034410;
        ret[2] = 12297829382473034410;
        ret[3] = 3074457345618258602;
    }
    return ret;
}

function get_ed25519_b(n, k) {
    assert(n == 64 && k == 4);
    var ret[100];
    if (n == 64 && k == 4) {
        ret[0] = 2741388824290576484;
        ret[1] = 17080318586768103348;
        ret[2] = 683212743470724133;
        ret[3] = 8881765665119413741;
    }
    return ret;
}

// returns G * 2 ** 255
// TODO check that this is correct...
// TODO update for ed25519, as needed
function get_dummy_point(n, k) {
    assert(n == 86 && k == 3 || n == 64 && k == 4);
    var ret[2][100]; // should be [2][k]
    if (k == 3) {
        ret[0][0] = 34318960048412842733519232;
        ret[0][1] = 3417427387252098100392906;
        ret[0][2] = 2056756886390887154635856;
        ret[1][0] = 35848273954982567597050105;
        ret[1][1] = 74802087901123421621824957;
        ret[1][2] = 4851915413831746153124691;
    } else {
        ret[0][0] = 10184385086782357888;
        ret[0][1] = 16068507144229249874;
        ret[0][2] = 17097072337414981695;
        ret[0][3] = 1961476217642676500;
        ret[1][0] = 15220267994978715897;
        ret[1][1] = 2812694141792528170;
        ret[1][2] = 9886878341545582154;
        ret[1][3] = 4627147115546938088;
    }
    return ret;
}

// a[0], a[1] = x1, y1
// b[0], b[1] = x2, y2
// lamb = (b[1] - a[1]) / (b[0] - a[0]) % p
// out[0] = lamb ** 2 - a[0] - b[0] % p
// out[1] = lamb * (a[0] - out[0]) - a[1] % p
function ed25519_addunequal_func(n, k, x1, y1, x2, y2){
    var a[2][100];
    var b[2][100];

    var x1_pos[100] = make_positive(n, k, x1);
    var y1_pos[100] = make_positive(n, k, y1);
    var x2_pos[100] = make_positive(n, k, x2);
    var y2_pos[100] = make_positive(n, k, y2);

    for(var i = 0; i < k; i++){
        a[0][i] = x1_pos[i];
        a[1][i] = y1_pos[i];
        b[0][i] = x2_pos[i];
        b[1][i] = y2_pos[i];
    }

    var out[2][100];

    var p[100] = get_ed25519_prime(n, k);

    // b[1] - a[1]
    var sub1_out[100] = long_sub_mod_p(n, k, b[1], a[1], p);

    // b[0] - a[0]
    var sub0_out[100]= long_sub_mod_p(n, k, b[0], a[0], p);

    // lambda = (b[1] - a[1]) * inv(b[0] - a[0])
    var sub0inv[100] = mod_inv(n, k, sub0_out, p);
    var lambda[100] = prod_mod_p(n, k, sub1_out, sub0inv, p);

    // out[0] = lambda ** 2 - a[0] - b[0]
    var lambdasq_out[100] = prod_mod_p(n, k, lambda, lambda, p);
    var out0_pre_out[100] = long_sub_mod_p(n, k, lambdasq_out, a[0], p);
    var out0_out[100] = long_sub_mod_p(n, k, out0_pre_out, b[0], p);
    for (var i = 0; i < k; i++) {
        out[0][i] = out0_out[i];
    }

    // out[1] = lambda * (a[0] - out[0]) - a[1]
    var out1_0_out[100] = long_sub_mod_p(n, k, a[0], out[0], p);
    var out1_1_out[100] = prod_mod_p(n, k, lambda, out1_0_out, p);
    var out1_out[100] = long_sub_mod_p(n, k, out1_1_out, a[1], p);
    for (var i = 0; i < k; i++) {
        out[1][i] = out1_out[i];
    }

    return out;
}

// a[0], a[1] = x1, y1
// lamb = (3 * a[0] ** 2 + a_ell) / (2 * a[1]) % p
// out[0] = lamb ** 2 - (2 * a[0]) % p
// out[1] = lamb * (a[0] - out[0]) - a[1] % p
function ed25519_double_func(n, k, x1, y1){
    var a[2][100];
    var b[2][100];

    var x1_pos[100] = make_positive(n, k, x1);
    var y1_pos[100] = make_positive(n, k, y1);

    // log("new y1_pos: ", y1_pos[0], y1_pos[1], y1_pos[2], y1_pos[3]);

    for(var i = 0; i < k; i++){
        a[0][i] = x1_pos[i];
        a[1][i] = y1_pos[i];
    }

    var out[2][100];

    var p[100] = get_ed25519_prime(n, k);
    var a_ell[100] = get_ed25519_a(n, k);

    // lamb_numer = 3 * a[0] ** 2 + a_ell
    var x1_sq[100] = prod_mod_p(n, k, a[0], a[0], p);
    var three[100];
    for (var i = 0; i < 100; i++) three[i] = i == 0 ? 3 : 0;
    var lamb_numer_temp[100] = prod_mod_p(n, k, x1_sq, three, p);
    var lamb_numer[100];
    for (var i = 0; i < 100; i++) { lamb_numer[i] = a_ell[i] + lamb_numer_temp[i]; }

    // lamb_denom = 2 * a[1]
    var two[100];
    for (var i = 0; i < 100; i++) two[i] = i == 0 ? 2 : 0;
    var lamb_denom[100] = prod_mod_p(n, k, a[1], two, p);

    // lambda = lamb_numer * inv(lamb_denom)
    var lamb_denom_inv[100] = mod_inv(n, k, lamb_denom, p);
    var lambda[100] = prod_mod_p(n, k, lamb_numer, lamb_denom_inv, p);

    // out[0] = lambda ** 2 - 2 * a[0]
    var lambdasq_out[100] = prod_mod_p(n, k, lambda, lambda, p);
    var out0_pre_out[100] = long_sub_mod_p(n, k, lambdasq_out, a[0], p);
    var out0_out[100] = long_sub_mod_p(n, k, out0_pre_out, a[0], p);
    for (var i = 0; i < k; i++) {
        out[0][i] = out0_out[i];
    }

    // out[1] = lambda * (a[0] - out[0]) - a[1]
    var out1_0_out[100] = long_sub_mod_p(n, k, a[0], out[0], p);
    var out1_1_out[100] = prod_mod_p(n, k, lambda, out1_0_out, p);
    var out1_out[100] = long_sub_mod_p(n, k, out1_1_out, a[1], p);
    for (var i = 0; i < k; i++) {
        out[1][i] = out1_out[i];
    }

    return out;
}


// Ensure that the mod-p value x is positive by adding the prime if it is negative
function make_positive(n, k, x) {
    assert(n == 64 && k == 4);
    var p[100] = get_ed25519_prime(n, k);
    var x2[5];
    for (var i = 0; i < k; i++) {
        x2[i] = x[i];
    }
    x2[4] = 0;
    for (var i = 0; i < k; i++) {
        x2[i + 1] += p[i];
    }
    // log("x2", x2[0], x2[1], x2[2], x2[3], x2[4]);
    // var x3[100] = getProperRepresentation_logging(100, n, 5, x2);
    // log("x3", x3[0], x3[1], x3[2], x3[3], x3[4], x3[5], x3[6], x3[7], x3[8], x3[9]);
    var x3[100] = getProperRepresentation(100, n, 5, x2);
    var div_out[2][100] = long_div(n, k, 10, x3, p);
    return div_out[1];
}


// // m bits per overflowed register (values are potentially negative)
// // n bits per properly-sized register
// // in has k registers
// // out has k + ceil(m/n) - 1 + 1 registers. highest-order potentially negative,
// // all others are positive
// // - 1 since the last register is included in the last ceil(m/n) array
// // + 1 since the carries from previous registers could push you over
// function getProperRepresentation_logging(m, n, k, in) {
//     var ceilMN = 0; // ceil(m/n)
//     if (m % n == 0) {
//         ceilMN = m \ n;
//     } else {
//         ceilMN = m \ n + 1;
//     }

//     var pieces[100][100]; // should be pieces[k][ceilMN]
//     for (var i = 0; i < k; i++) {
//         for (var j = 0; j < 100; j++) {
//             pieces[i][j] = 0;
//         }
//         if (isNegative(in[i]) == 1) {
//             // log("negative input: ", i, in[i], -1 * in[i]);
//             var negPieces[100] = splitOverflowedRegister(m, n, -1 * in[i]);
//             for (var j = 0; j < ceilMN; j++) {
//                 pieces[i][j] = -1 * negPieces[j];
//             }
//         } else {
//             // var t1 = (in[i] < 0 ? 1 : 0);
//             // var t2 = (in[i] > 10944121435919637611123202872628637544274182200208017171849102093287904247808 ? 1 : 0);
//             // log("positive input: ", i, in[i], -1 * in[i], isNegative(in[i]), t1, t2);
//             pieces[i] = splitOverflowedRegister(m, n, in[i]);
//         }
//     }

//     var out[100]; // should be out[k + ceilMN]
//     var carries[100]; // should be carries[k + ceilMN]
//     for (var i = 0; i < 100; i++) {
//         out[i] = 0;
//         carries[i] = 0;
//     }
//     for (var registerIdx = 0; registerIdx < k + ceilMN; registerIdx++) {
//         var thisRegisterValue = 0;
//         if (registerIdx > 0) {
//             thisRegisterValue = carries[registerIdx - 1];
//         }

//         var start = 0;
//         if (registerIdx >= ceilMN) {
//             start = registerIdx - ceilMN + 1;
//         }

//         // go from start to min(registerIdx, len(pieces)-1)
//         for (var i = start; i <= registerIdx; i++) {
//             if (i < k) {
//                 thisRegisterValue += pieces[i][registerIdx - i];
//             }
//         }

//         if (isNegative(thisRegisterValue) == 1) {
//             var thisRegisterAbs = -1 * thisRegisterValue;
//             out[registerIdx] = (1<<n) - (thisRegisterAbs % (1<<n));
//             carries[registerIdx] = -1 * (thisRegisterAbs >> n) - 1;
//         } else {
//             out[registerIdx] = thisRegisterValue % (1<<n);
//             carries[registerIdx] = thisRegisterValue >> n;
//         }
//     }

//     return out;
// }