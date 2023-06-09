/* Limbs of the secp256k1 order. */
#define SECP256K1_N_0 ((ulong)0xBFD25E8CD0364141UL)
#define SECP256K1_N_1 ((ulong)0xBAAEDCE6AF48A03BUL)
#define SECP256K1_N_2 ((ulong)0xFFFFFFFFFFFFFFFEUL)
#define SECP256K1_N_3 ((ulong)0xFFFFFFFFFFFFFFFFUL)

/* Limbs of 2^256 minus the secp256k1 order. */
#define SECP256K1_N_C_0 (~SECP256K1_N_0 + 1)
#define SECP256K1_N_C_1 (~SECP256K1_N_1)
#define SECP256K1_N_C_2 (1)

/* Limbs of half the secp256k1 order. */
#define SECP256K1_N_H_0 ((ulong)0xDFE92F46681B20A0UL)
#define SECP256K1_N_H_1 ((ulong)0x5D576E7357A4501DUL)
#define SECP256K1_N_H_2 ((ulong)0xFFFFFFFFFFFFFFFFUL)
#define SECP256K1_N_H_3 ((ulong)0x7FFFFFFFFFFFFFFFUL)

/* Determine the number of trailing zero bits in a (non-zero) 64-bit x.
 * This function is only intended to be used as fallback for
 * secp256k1_ctz64_var, but permits it to be tested separately. */
__constant uchar debruijn[64] = {
	0, 1, 2, 53, 3, 7, 54, 27, 4, 38, 41, 8, 34, 55, 48, 28,
	62, 5, 39, 46, 44, 42, 22, 9, 24, 35, 59, 56, 49, 18, 29, 11,
	63, 52, 6, 26, 37, 40, 33, 47, 61, 45, 43, 21, 23, 58, 17, 10,
	51, 25, 36, 32, 60, 20, 57, 16, 50, 31, 19, 15, 30, 14, 13, 12
};
static int secp256k1_ctz64_var_debruijn(ulong x) {
    return debruijn[(ulong)((x & -x) * 0x022FDD63CC95386DUL) >> 58];
}

/** The number of entries a table with precomputed multiples needs to have. */
static long ECMULT_TABLE_SIZE(int w) {
	return (1L << ((w)-2));
}

/** Larger values for ECMULT_WINDOW_SIZE result in possibly better
 *  performance at the cost of an exponentially larger precomputed
 *  table. The exact table size is
 *      (1 << (WINDOW_G - 2)) * sizeof(secp256k1_ge_storage)  bytes,
 *  where sizeof(secp256k1_ge_storage) is typically 64 bytes but can
 *  be larger due to platform-specific padding and alignment.
 *  Two tables of this size are used (due to the endomorphism
 *  optimization).                                                    */
#define WINDOW_A 5
#define WINDOW_G 15

/* int128 and uint128 implementation */
typedef struct { ulong hi; ulong lo; } secp256k1_uint128;
typedef struct { long hi; ulong lo; } secp256k1_int128;
static void secp256k1_u128_add(secp256k1_uint128 *r, const secp256k1_uint128 *a, const secp256k1_uint128 *b) {
    uchar carry;

    r->lo = a->lo + b->lo;
    carry = (r->lo < a->lo) || (r->lo < b->lo);

    r->hi = a->hi + b->hi + carry;
}
static void secp256k1_u128_mul(secp256k1_uint128 *r, ulong a, ulong b) {
    ulong lowPart = (ulong)a * (ulong)b;
	ulong highPart = mul_hi(a, b);

	r->lo = lowPart;
	r->hi = highPart;
}
static void secp256k1_u128_accum_u64(secp256k1_uint128 *r, ulong a) {
    uchar carry;
	r->lo = r->lo + a;
	carry = (r->lo < a);
	r->hi = r->hi + carry;
}
static void secp256k1_u128_accum_mul(secp256k1_uint128 *r, ulong a, ulong b) {
    secp256k1_uint128 ab;
    secp256k1_u128_mul(&ab, a, b);

    secp256k1_uint128 temp = *r;
    secp256k1_u128_add(&temp, &temp, &ab);
    *r = temp;
}

// NEEDS TESTING (negative carry)
static void secp256k1_i128_add(secp256k1_int128 *r, const secp256k1_int128 *a, const secp256k1_int128 *b) {
    uchar carry;

    r->lo = a->lo + b->lo;
    carry = (r->lo < a->lo) || (r->lo < b->lo);

    r->hi = a->hi + b->hi + carry;
}
static void secp256k1_i128_mul(secp256k1_int128 *r, long a, long b) {
    ulong lowPart = (ulong)a * (ulong)b;
	long highPart = mul_hi(a, b);

	r->lo = lowPart;
	r->hi = highPart;
}
static void secp256k1_i128_accum_mul(secp256k1_int128 *r, long a, long b) {
    secp256k1_int128 ab;
    secp256k1_i128_mul(&ab, a, b);

    secp256k1_int128 temp = *r;
    secp256k1_i128_add(&temp, &temp, &ab);
    *r = temp;
}

// NEEDS TESTING
static ulong secp256k1_i128_to_u64(const secp256k1_int128 *a) {
    return a->lo;
}

static void secp256k1_u128_from_u64(secp256k1_uint128 *r, ulong a) {
    r->lo = a;
}

// NEEDS TESTING (check negative)
static long secp256k1_i128_to_i64(const secp256k1_int128 *a) {
    return (long)a->lo;
}

static ulong secp256k1_u128_to_u64(const secp256k1_uint128 *a) {
   return a->lo;
}

// NEEDS TESTING
static void secp256k1_i128_rshift(secp256k1_int128 *r, unsigned int n) {
	r->hi >>= n;
	r->hi |= r->lo << (64 - n);
	r->lo >>= n;
}

// NEEDS TESTING (check negative)
static void secp256k1_u128_rshift(secp256k1_uint128 *r, unsigned int n) {
	r->hi >>= n;
	r->hi |= r->lo << (64 - n);
	r->lo >>= n;
}

// NEEDS TESTING
static ulong secp256k1_u128_hi_u64(const secp256k1_uint128 *a) {
   return a->hi;
}


/* A signed 62-bit limb representation of integers. Its value is sum(v[i] * 2^(62*i), i=0..4). */
typedef struct {
    long v[5];
} secp256k1_modinv64_signed62;
typedef struct {
    /* The modulus in signed62 notation, must be odd and in [3, 2^256]. */
    secp256k1_modinv64_signed62 modulus;
    ulong modulus_inv62; /* modulus^{-1} mod 2^62 */
} secp256k1_modinv64_modinfo;
__constant secp256k1_modinv64_modinfo secp256k1_const_modinfo_scalar = {
    {{0x3FD25E8CD0364141LL, 0x2ABB739ABD2280EELL, -0x15LL, 0, 256}},
    0x34F20099AA774EC1LL
};
typedef struct {
    long u, v, q, r;
} secp256k1_modinv64_trans2x2;
static long secp256k1_modinv64_divsteps_62_var(long eta, ulong f0, ulong g0, secp256k1_modinv64_trans2x2 *t) {
    ulong u = 1, v = 0, q = 0, r = 1;
    ulong f = f0, g = g0, m;
    uint w;
    int i = 62, limit, zeros;
    for (;;) {
        /* Use a sentinel bit to count zeros only up to i. */
        zeros = secp256k1_ctz64_var_debruijn(g | (ULONG_MAX << i));
        /* Perform zeros divsteps at once; they all just divide g by two. */
        g >>= zeros;
        u <<= zeros;
        v <<= zeros;
        eta -= zeros;
        i -= zeros;
        /* We're done once we've done 62 divsteps. */
        if (i == 0) break;
        /* If eta is negative, negate it and replace f,g with g,-f. */
        if (eta < 0) {
            ulong tmp;
            eta = -eta;
            tmp = f; f = g; g = -tmp;
            tmp = u; u = q; q = -tmp;
            tmp = v; v = r; r = -tmp;
            /* Use a formula to cancel out up to 6 bits of g. Also, no more than i can be cancelled
             * out (as we'd be done before that point), and no more than eta+1 can be done as its
             * sign will flip again once that happens. */
            limit = ((int)eta + 1) > i ? i : ((int)eta + 1);
            /* m is a mask for the bottom min(limit, 6) bits. */
            m = (ULONG_MAX >> (64 - limit)) & 63U;
            /* Find what multiple of f must be added to g to cancel its bottom min(limit, 6) bits. */
            w = (f * g * (f * f - 2)) & m;
        } else {
            /* In this branch, use a simpler formula that only lets us cancel up to 4 bits of g, as eta tends to be smaller here. */
            limit = ((int)eta + 1) > i ? i : ((int)eta + 1);
            /* m is a mask for the bottom min(limit, 4) bits. */
            m = (ULONG_MAX >> (64 - limit)) & 15U;
            /* Find what multiple of f must be added to g to cancel its bottom min(limit, 4) bits. */
            w = f + (((f + 1) & 4) << 1);
            w = (-w * g) & m;
        }
        g += f * w;
        q += u * w;
        r += v * w;
    }
    /* Return data in t and return value. */
    t->u = (long)u;
    t->v = (long)v;
    t->q = (long)q;
    t->r = (long)r;
    return eta;
}
static void secp256k1_modinv64_update_de_62(secp256k1_modinv64_signed62 *d, secp256k1_modinv64_signed62 *e, const secp256k1_modinv64_trans2x2 *t, __constant secp256k1_modinv64_modinfo* modinfo) {
    const ulong M62 = ULONG_MAX >> 2;
    const long d0 = d->v[0], d1 = d->v[1], d2 = d->v[2], d3 = d->v[3], d4 = d->v[4];
    const long e0 = e->v[0], e1 = e->v[1], e2 = e->v[2], e3 = e->v[3], e4 = e->v[4];
    const long u = t->u, v = t->v, q = t->q, r = t->r;
    long md, me, sd, se;
    secp256k1_int128 cd, ce;

    /* [md,me] start as zero; plus [u,q] if d is negative; plus [v,r] if e is negative. */
    sd = d4 >> 63;
    se = e4 >> 63;
    md = (u & sd) + (v & se);
    me = (q & sd) + (r & se);
    /* Begin computing t*[d,e]. */
    secp256k1_i128_mul(&cd, u, d0);
    secp256k1_i128_accum_mul(&cd, v, e0);
    secp256k1_i128_mul(&ce, q, d0);
    secp256k1_i128_accum_mul(&ce, r, e0);
    /* Correct md,me so that t*[d,e]+modulus*[md,me] has 62 zero bottom bits. */
    md -= (modinfo->modulus_inv62 * secp256k1_i128_to_u64(&cd) + md) & M62;
    me -= (modinfo->modulus_inv62 * secp256k1_i128_to_u64(&ce) + me) & M62;
    /* Update the beginning of computation for t*[d,e]+modulus*[md,me] now md,me are known. */
    secp256k1_i128_accum_mul(&cd, modinfo->modulus.v[0], md);
    secp256k1_i128_accum_mul(&ce, modinfo->modulus.v[0], me);
    /* Verify that the low 62 bits of the computation are indeed zero, and then throw them away. */
    secp256k1_i128_rshift(&cd, 62);
    secp256k1_i128_rshift(&ce, 62);
    /* Compute limb 1 of t*[d,e]+modulus*[md,me], and store it as output limb 0 (= down shift). */
    secp256k1_i128_accum_mul(&cd, u, d1);
    secp256k1_i128_accum_mul(&cd, v, e1);
    secp256k1_i128_accum_mul(&ce, q, d1);
    secp256k1_i128_accum_mul(&ce, r, e1);
    if (modinfo->modulus.v[1]) { /* Optimize for the case where limb of modulus is zero. */
        secp256k1_i128_accum_mul(&cd, modinfo->modulus.v[1], md);
        secp256k1_i128_accum_mul(&ce, modinfo->modulus.v[1], me);
    }
    d->v[0] = secp256k1_i128_to_u64(&cd) & M62; secp256k1_i128_rshift(&cd, 62);
    e->v[0] = secp256k1_i128_to_u64(&ce) & M62; secp256k1_i128_rshift(&ce, 62);
    /* Compute limb 2 of t*[d,e]+modulus*[md,me], and store it as output limb 1. */
    secp256k1_i128_accum_mul(&cd, u, d2);
    secp256k1_i128_accum_mul(&cd, v, e2);
    secp256k1_i128_accum_mul(&ce, q, d2);
    secp256k1_i128_accum_mul(&ce, r, e2);
    if (modinfo->modulus.v[2]) { /* Optimize for the case where limb of modulus is zero. */
        secp256k1_i128_accum_mul(&cd, modinfo->modulus.v[2], md);
        secp256k1_i128_accum_mul(&ce, modinfo->modulus.v[2], me);
    }
    d->v[1] = secp256k1_i128_to_u64(&cd) & M62; secp256k1_i128_rshift(&cd, 62);
    e->v[1] = secp256k1_i128_to_u64(&ce) & M62; secp256k1_i128_rshift(&ce, 62);
    /* Compute limb 3 of t*[d,e]+modulus*[md,me], and store it as output limb 2. */
    secp256k1_i128_accum_mul(&cd, u, d3);
    secp256k1_i128_accum_mul(&cd, v, e3);
    secp256k1_i128_accum_mul(&ce, q, d3);
    secp256k1_i128_accum_mul(&ce, r, e3);
    if (modinfo->modulus.v[3]) { /* Optimize for the case where limb of modulus is zero. */
        secp256k1_i128_accum_mul(&cd, modinfo->modulus.v[3], md);
        secp256k1_i128_accum_mul(&ce, modinfo->modulus.v[3], me);
    }
    d->v[2] = secp256k1_i128_to_u64(&cd) & M62; secp256k1_i128_rshift(&cd, 62);
    e->v[2] = secp256k1_i128_to_u64(&ce) & M62; secp256k1_i128_rshift(&ce, 62);
    /* Compute limb 4 of t*[d,e]+modulus*[md,me], and store it as output limb 3. */
    secp256k1_i128_accum_mul(&cd, u, d4);
    secp256k1_i128_accum_mul(&cd, v, e4);
    secp256k1_i128_accum_mul(&ce, q, d4);
    secp256k1_i128_accum_mul(&ce, r, e4);
    secp256k1_i128_accum_mul(&cd, modinfo->modulus.v[4], md);
    secp256k1_i128_accum_mul(&ce, modinfo->modulus.v[4], me);
    d->v[3] = secp256k1_i128_to_u64(&cd) & M62; secp256k1_i128_rshift(&cd, 62);
    e->v[3] = secp256k1_i128_to_u64(&ce) & M62; secp256k1_i128_rshift(&ce, 62);
    /* What remains is limb 5 of t*[d,e]+modulus*[md,me]; store it as output limb 4. */
    d->v[4] = secp256k1_i128_to_i64(&cd);
    e->v[4] = secp256k1_i128_to_i64(&ce);
}
static void secp256k1_modinv64_update_fg_62_var(int len, secp256k1_modinv64_signed62 *f, secp256k1_modinv64_signed62 *g, const secp256k1_modinv64_trans2x2 *t) {
    const ulong M62 = ULONG_MAX >> 2;
    const long u = t->u, v = t->v, q = t->q, r = t->r;
    long fi, gi;
    secp256k1_int128 cf, cg;
    int i;
    /* Start computing t*[f,g]. */
    fi = f->v[0];
    gi = g->v[0];
    secp256k1_i128_mul(&cf, u, fi);
    secp256k1_i128_accum_mul(&cf, v, gi);
    secp256k1_i128_mul(&cg, q, fi);
    secp256k1_i128_accum_mul(&cg, r, gi);
    /* Verify that the bottom 62 bits of the result are zero, and then throw them away. */
    secp256k1_i128_rshift(&cf, 62);
    secp256k1_i128_rshift(&cg, 62);
    /* Now iteratively compute limb i=1..len of t*[f,g], and store them in output limb i-1 (shifting
     * down by 62 bits). */
    for (i = 1; i < len; ++i) {
        fi = f->v[i];
        gi = g->v[i];
        secp256k1_i128_accum_mul(&cf, u, fi);
        secp256k1_i128_accum_mul(&cf, v, gi);
        secp256k1_i128_accum_mul(&cg, q, fi);
        secp256k1_i128_accum_mul(&cg, r, gi);
        f->v[i - 1] = secp256k1_i128_to_u64(&cf) & M62; secp256k1_i128_rshift(&cf, 62);
        g->v[i - 1] = secp256k1_i128_to_u64(&cg) & M62; secp256k1_i128_rshift(&cg, 62);
    }
    /* What remains is limb (len) of t*[f,g]; store it as output limb (len-1). */
    f->v[len - 1] = secp256k1_i128_to_i64(&cf);
    g->v[len - 1] = secp256k1_i128_to_i64(&cg);
}
static void secp256k1_modinv64_normalize_62(secp256k1_modinv64_signed62 *r, long sign, __constant secp256k1_modinv64_modinfo *modinfo) {
    const long M62 = (long)(ULONG_MAX >> 2);
    long r0 = r->v[0], r1 = r->v[1], r2 = r->v[2], r3 = r->v[3], r4 = r->v[4];
    
	// NEEDS TESTING, remove volatile keyword
	long cond_add, cond_negate;

    /* In a first step, add the modulus if the input is negative, and then negate if requested.
     * This brings r from range (-2*modulus,modulus) to range (-modulus,modulus). As all input
     * limbs are in range (-2^62,2^62), this cannot overflow an int64_t. Note that the right
     * shifts below are signed sign-extending shifts (see assumptions.h for tests that that is
     * indeed the behavior of the right shift operator). */
    cond_add = r4 >> 63;
    r0 += modinfo->modulus.v[0] & cond_add;
    r1 += modinfo->modulus.v[1] & cond_add;
    r2 += modinfo->modulus.v[2] & cond_add;
    r3 += modinfo->modulus.v[3] & cond_add;
    r4 += modinfo->modulus.v[4] & cond_add;
    cond_negate = sign >> 63;
    r0 = (r0 ^ cond_negate) - cond_negate;
    r1 = (r1 ^ cond_negate) - cond_negate;
    r2 = (r2 ^ cond_negate) - cond_negate;
    r3 = (r3 ^ cond_negate) - cond_negate;
    r4 = (r4 ^ cond_negate) - cond_negate;
    /* Propagate the top bits, to bring limbs back to range (-2^62,2^62). */
    r1 += r0 >> 62; r0 &= M62;
    r2 += r1 >> 62; r1 &= M62;
    r3 += r2 >> 62; r2 &= M62;
    r4 += r3 >> 62; r3 &= M62;

    /* In a second step add the modulus again if the result is still negative, bringing
     * r to range [0,modulus). */
    cond_add = r4 >> 63;
    r0 += modinfo->modulus.v[0] & cond_add;
    r1 += modinfo->modulus.v[1] & cond_add;
    r2 += modinfo->modulus.v[2] & cond_add;
    r3 += modinfo->modulus.v[3] & cond_add;
    r4 += modinfo->modulus.v[4] & cond_add;
    /* And propagate again. */
    r1 += r0 >> 62; r0 &= M62;
    r2 += r1 >> 62; r1 &= M62;
    r3 += r2 >> 62; r2 &= M62;
    r4 += r3 >> 62; r3 &= M62;

    r->v[0] = r0;
    r->v[1] = r1;
    r->v[2] = r2;
    r->v[3] = r3;
    r->v[4] = r4;
}
static void secp256k1_modinv64_var(secp256k1_modinv64_signed62 *x, __constant secp256k1_modinv64_modinfo *modinfo) {
    /* Start with d=0, e=1, f=modulus, g=x, eta=-1. */
    secp256k1_modinv64_signed62 d = {{0, 0, 0, 0, 0}};
    secp256k1_modinv64_signed62 e = {{1, 0, 0, 0, 0}};
    secp256k1_modinv64_signed62 f = modinfo->modulus;
    secp256k1_modinv64_signed62 g = *x;

    int j, len = 5;
    ulong eta = -1; /* eta = -delta; delta is initially 1 */
    ulong cond, fn, gn;

    /* Do iterations of 62 divsteps each until g=0. */
    while (1) {
        /* Compute transition matrix and new eta after 62 divsteps. */
        secp256k1_modinv64_trans2x2 t;
        eta = secp256k1_modinv64_divsteps_62_var(eta, f.v[0], g.v[0], &t);
        /* Update d,e using that transition matrix. */
        secp256k1_modinv64_update_de_62(&d, &e, &t, modinfo);
        /* Update f,g using that transition matrix. */
        secp256k1_modinv64_update_fg_62_var(len, &f, &g, &t);
        /* If the bottom limb of g is zero, there is a chance that g=0. */
        if (g.v[0] == 0) {
            cond = 0;
            /* Check if the other limbs are also 0. */
            for (j = 1; j < len; ++j) {
                cond |= g.v[j];
            }
            /* If so, we're done. */
            if (cond == 0) break;
        }

        /* Determine if len>1 and limb (len-1) of both f and g is 0 or -1. */
        fn = f.v[len - 1];
        gn = g.v[len - 1];
        cond = ((long)len - 2) >> 63;
        cond |= fn ^ (fn >> 63);
        cond |= gn ^ (gn >> 63);
        /* If so, reduce length, propagating the sign of f and g's top limb into the one below. */
        if (cond == 0) {
            f.v[len - 2] |= (ulong)fn << 62;
            g.v[len - 2] |= (ulong)gn << 62;
            --len;
        }
    }

    /* Optionally negate d, normalize to [0,modulus), and return it. */
    secp256k1_modinv64_normalize_62(&d, f.v[len - 1], modinfo);
    *x = d;
}

/** This field implementation represents the value as 5 ulong limbs in base
 *  2^52. */
typedef struct {
   /* A field element f represents the sum(i=0..4, f.n[i] << (i*52)) mod p,
    * where p is the field modulus, 2^256 - 2^32 - 977.
    *
    * The individual limbs f.n[i] can exceed 2^52; the field's magnitude roughly
    * corresponds to how much excess is allowed. The value
    * sum(i=0..4, f.n[i] << (i*52)) may exceed p, unless the field element is
    * normalized. */
    ulong n[5];
} secp256k1_fe;

// NEEDS TESTING - Check the constant (added leading 0)
__constant secp256k1_fe const_beta = {{ 0, 0x7AE96A2B657C0710UL, 0x6E64479EAC3434E9UL, 0x9CF0497512F58995UL, 0xC1396C28719501EEUL }};
__constant secp256k1_fe secp256k1_ecdsa_const_p_minus_order = {{ 0, 0, 1, 0x4551231950B75FC4UL, 0x402DA1722FC9BAEEUL }};
__constant secp256k1_fe secp256k1_ecdsa_const_order_as_fe = {{ 0, 0xFFFFFFFFFFFFFFFFUL, 0xFFFFFFFFFFFFFFFEUL, 0xBAAEDCE6AF48A03BUL, 0xBFD25E8CD0364141UL }};
typedef struct {
    secp256k1_fe x;
    secp256k1_fe y;
    int infinity; /* whether this represents the point at infinity */
} secp256k1_ge;
typedef struct {
    secp256k1_fe x; /* actual X: x/z^2 */
    secp256k1_fe y; /* actual Y: y/z^3 */
    secp256k1_fe z;
    int infinity; /* whether this represents the point at infinity */
} secp256k1_gej;
typedef struct { ulong n[4]; } secp256k1_fe_storage;
typedef struct {
    secp256k1_fe_storage x;
    secp256k1_fe_storage y;
} secp256k1_ge_storage;

// Have to hardcode size
//__constant secp256k1_ge_storage secp256k1_pre_g[ECMULT_TABLE_SIZE(WINDOW_G)];
__constant secp256k1_ge_storage secp256k1_pre_g[8192];
__constant secp256k1_ge_storage secp256k1_pre_g_128[8192];

static void secp256k1_fe_set_int(secp256k1_fe *r, int a) {
    r->n[0] = a;
    r->n[1] = r->n[2] = r->n[3] = r->n[4] = 0;
}
static void secp256k1_fe_clear(secp256k1_fe *a) {
    a->n[0]=0; a->n[1]=0; a->n[2]=0; a->n[3]=0; a->n[4]=0;
}
static void secp256k1_fe_set_b32_mod(secp256k1_fe *r, const uchar *a) {
    r->n[0] = (ulong)a[31]
            | ((ulong)a[30] << 8)
            | ((ulong)a[29] << 16)
            | ((ulong)a[28] << 24)
            | ((ulong)a[27] << 32)
            | ((ulong)a[26] << 40)
            | ((ulong)(a[25] & 0xF)  << 48);
    r->n[1] = (ulong)((a[25] >> 4) & 0xF)
            | ((ulong)a[24] << 4)
            | ((ulong)a[23] << 12)
            | ((ulong)a[22] << 20)
            | ((ulong)a[21] << 28)
            | ((ulong)a[20] << 36)
            | ((ulong)a[19] << 44);
    r->n[2] = (ulong)a[18]
            | ((ulong)a[17] << 8)
            | ((ulong)a[16] << 16)
            | ((ulong)a[15] << 24)
            | ((ulong)a[14] << 32)
            | ((ulong)a[13] << 40)
            | ((ulong)(a[12] & 0xF) << 48);
    r->n[3] = (ulong)((a[12] >> 4) & 0xF)
            | ((ulong)a[11] << 4)
            | ((ulong)a[10] << 12)
            | ((ulong)a[9]  << 20)
            | ((ulong)a[8]  << 28)
            | ((ulong)a[7]  << 36)
            | ((ulong)a[6]  << 44);
    r->n[4] = (ulong)a[5]
            | ((ulong)a[4] << 8)
            | ((ulong)a[3] << 16)
            | ((ulong)a[2] << 24)
            | ((ulong)a[1] << 32)
            | ((ulong)a[0] << 40);
}
static int secp256k1_fe_set_b32_limit(secp256k1_fe *r, const uchar *a) {
    secp256k1_fe_set_b32_mod(r, a);
    return !((r->n[4] == 0x0FFFFFFFFFFFFUL) & ((r->n[3] & r->n[2] & r->n[1]) == 0xFFFFFFFFFFFFFUL) & (r->n[0] >= 0xFFFFEFFFFFC2FUL));
}
static void secp256k1_fe_from_storage(secp256k1_fe *r, const secp256k1_fe_storage *a) {
    r->n[0] = a->n[0] & 0xFFFFFFFFFFFFFUL;
    r->n[1] = a->n[0] >> 52 | ((a->n[1] << 12) & 0xFFFFFFFFFFFFFUL);
    r->n[2] = a->n[1] >> 40 | ((a->n[2] << 24) & 0xFFFFFFFFFFFFFUL);
    r->n[3] = a->n[2] >> 28 | ((a->n[3] << 36) & 0xFFFFFFFFFFFFFUL);
    r->n[4] = a->n[3] >> 16;
}
static void secp256k1_fe_from_storage_const(secp256k1_fe *r, __constant const secp256k1_fe_storage *a) {
    r->n[0] = a->n[0] & 0xFFFFFFFFFFFFFUL;
    r->n[1] = a->n[0] >> 52 | ((a->n[1] << 12) & 0xFFFFFFFFFFFFFUL);
    r->n[2] = a->n[1] >> 40 | ((a->n[2] << 24) & 0xFFFFFFFFFFFFFUL);
    r->n[3] = a->n[2] >> 28 | ((a->n[3] << 36) & 0xFFFFFFFFFFFFFUL);
    r->n[4] = a->n[3] >> 16;
}
static void secp256k1_fe_add(secp256k1_fe *r, const secp256k1_fe *a) {
    r->n[0] += a->n[0];
    r->n[1] += a->n[1];
    r->n[2] += a->n[2];
    r->n[3] += a->n[3];
    r->n[4] += a->n[4];
}
static void secp256k1_fe_add_const(secp256k1_fe *r, __constant const secp256k1_fe *a) {
    r->n[0] += a->n[0];
    r->n[1] += a->n[1];
    r->n[2] += a->n[2];
    r->n[3] += a->n[3];
    r->n[4] += a->n[4];
}
static void secp256k1_fe_sqr_inner(ulong *r, const ulong *a) {
    secp256k1_uint128 c, d;
    ulong a0 = a[0], a1 = a[1], a2 = a[2], a3 = a[3], a4 = a[4];
    long t3, t4, tx, u0;
    const ulong M = 0xFFFFFFFFFFFFFUL, R = 0x1000003D10UL;

    /**  [... a b c] is a shorthand for ... + a<<104 + b<<52 + c<<0 mod n.
     *  px is a shorthand for sum(a[i]*a[x-i], i=0..x).
     *  Note that [x 0 0 0 0 0] = [x*R].
     */

    secp256k1_u128_mul(&d, a0*2, a3);
    secp256k1_u128_accum_mul(&d, a1*2, a2);
    /* [d 0 0 0] = [p3 0 0 0] */
    secp256k1_u128_mul(&c, a4, a4);
    /* [c 0 0 0 0 d 0 0 0] = [p8 0 0 0 0 p3 0 0 0] */
    secp256k1_u128_accum_mul(&d, R, secp256k1_u128_to_u64(&c)); secp256k1_u128_rshift(&c, 64);
    /* [(c<<12) 0 0 0 0 0 d 0 0 0] = [p8 0 0 0 0 p3 0 0 0] */
    t3 = secp256k1_u128_to_u64(&d) & M; secp256k1_u128_rshift(&d, 52);
    /* [(c<<12) 0 0 0 0 d t3 0 0 0] = [p8 0 0 0 0 p3 0 0 0] */

    a4 *= 2;
    secp256k1_u128_accum_mul(&d, a0, a4);
    secp256k1_u128_accum_mul(&d, a1*2, a3);
    secp256k1_u128_accum_mul(&d, a2, a2);
    /* [(c<<12) 0 0 0 0 d t3 0 0 0] = [p8 0 0 0 p4 p3 0 0 0] */
    secp256k1_u128_accum_mul(&d, R << 12, secp256k1_u128_to_u64(&c));
    /* [d t3 0 0 0] = [p8 0 0 0 p4 p3 0 0 0] */
    t4 = secp256k1_u128_to_u64(&d) & M; secp256k1_u128_rshift(&d, 52);
    /* [d t4 t3 0 0 0] = [p8 0 0 0 p4 p3 0 0 0] */
    tx = (t4 >> 48); t4 &= (M >> 4);
    /* [d t4+(tx<<48) t3 0 0 0] = [p8 0 0 0 p4 p3 0 0 0] */

    secp256k1_u128_mul(&c, a0, a0);
    /* [d t4+(tx<<48) t3 0 0 c] = [p8 0 0 0 p4 p3 0 0 p0] */
    secp256k1_u128_accum_mul(&d, a1, a4);
    secp256k1_u128_accum_mul(&d, a2*2, a3);
    /* [d t4+(tx<<48) t3 0 0 c] = [p8 0 0 p5 p4 p3 0 0 p0] */
    u0 = secp256k1_u128_to_u64(&d) & M; secp256k1_u128_rshift(&d, 52);
    /* [d u0 t4+(tx<<48) t3 0 0 c] = [p8 0 0 p5 p4 p3 0 0 p0] */
    /* [d 0 t4+(tx<<48)+(u0<<52) t3 0 0 c] = [p8 0 0 p5 p4 p3 0 0 p0] */
    u0 = (u0 << 4) | tx;
    /* [d 0 t4+(u0<<48) t3 0 0 c] = [p8 0 0 p5 p4 p3 0 0 p0] */
    secp256k1_u128_accum_mul(&c, u0, R >> 4);
    /* [d 0 t4 t3 0 0 c] = [p8 0 0 p5 p4 p3 0 0 p0] */
    r[0] = secp256k1_u128_to_u64(&c) & M; secp256k1_u128_rshift(&c, 52);
    /* [d 0 t4 t3 0 c r0] = [p8 0 0 p5 p4 p3 0 0 p0] */

    a0 *= 2;
    secp256k1_u128_accum_mul(&c, a0, a1);
    /* [d 0 t4 t3 0 c r0] = [p8 0 0 p5 p4 p3 0 p1 p0] */
    secp256k1_u128_accum_mul(&d, a2, a4);
    secp256k1_u128_accum_mul(&d, a3, a3);
    /* [d 0 t4 t3 0 c r0] = [p8 0 p6 p5 p4 p3 0 p1 p0] */
    secp256k1_u128_accum_mul(&c, secp256k1_u128_to_u64(&d) & M, R); secp256k1_u128_rshift(&d, 52);
    /* [d 0 0 t4 t3 0 c r0] = [p8 0 p6 p5 p4 p3 0 p1 p0] */
    r[1] = secp256k1_u128_to_u64(&c) & M; secp256k1_u128_rshift(&c, 52);
    /* [d 0 0 t4 t3 c r1 r0] = [p8 0 p6 p5 p4 p3 0 p1 p0] */

    secp256k1_u128_accum_mul(&c, a0, a2);
    secp256k1_u128_accum_mul(&c, a1, a1);
    /* [d 0 0 t4 t3 c r1 r0] = [p8 0 p6 p5 p4 p3 p2 p1 p0] */
    secp256k1_u128_accum_mul(&d, a3, a4);
    /* [d 0 0 t4 t3 c r1 r0] = [p8 p7 p6 p5 p4 p3 p2 p1 p0] */
    secp256k1_u128_accum_mul(&c, R, secp256k1_u128_to_u64(&d)); secp256k1_u128_rshift(&d, 64);
    /* [(d<<12) 0 0 0 t4 t3 c r1 r0] = [p8 p7 p6 p5 p4 p3 p2 p1 p0] */
    r[2] = secp256k1_u128_to_u64(&c) & M; secp256k1_u128_rshift(&c, 52);
    /* [(d<<12) 0 0 0 t4 t3+c r2 r1 r0] = [p8 p7 p6 p5 p4 p3 p2 p1 p0] */

    secp256k1_u128_accum_mul(&c, R << 12, secp256k1_u128_to_u64(&d));
    secp256k1_u128_accum_u64(&c, t3);
    /* [t4 c r2 r1 r0] = [p8 p7 p6 p5 p4 p3 p2 p1 p0] */
    r[3] = secp256k1_u128_to_u64(&c) & M; secp256k1_u128_rshift(&c, 52);
    /* [t4+c r3 r2 r1 r0] = [p8 p7 p6 p5 p4 p3 p2 p1 p0] */
    r[4] = secp256k1_u128_to_u64(&c) + t4;
    /* [r4 r3 r2 r1 r0] = [p8 p7 p6 p5 p4 p3 p2 p1 p0] */
}
static void secp256k1_fe_sqr(secp256k1_fe *r, const secp256k1_fe *a) {
    secp256k1_fe_sqr_inner(r->n, a->n);
}
static void secp256k1_fe_mul_inner(ulong *r, const ulong *a, const ulong *b) {
    secp256k1_uint128 c, d;
    ulong t3, t4, tx, u0;
    ulong a0 = a[0], a1 = a[1], a2 = a[2], a3 = a[3], a4 = a[4];
    const ulong M = 0xFFFFFFFFFFFFFUL, R = 0x1000003D10UL;

    /*  [... a b c] is a shorthand for ... + a<<104 + b<<52 + c<<0 mod n.
     *  for 0 <= x <= 4, px is a shorthand for sum(a[i]*b[x-i], i=0..x).
     *  for 4 <= x <= 8, px is a shorthand for sum(a[i]*b[x-i], i=(x-4)..4)
     *  Note that [x 0 0 0 0 0] = [x*R].
     */

    secp256k1_u128_mul(&d, a0, b[3]);
    secp256k1_u128_accum_mul(&d, a1, b[2]);
    secp256k1_u128_accum_mul(&d, a2, b[1]);
    secp256k1_u128_accum_mul(&d, a3, b[0]);
    /* [d 0 0 0] = [p3 0 0 0] */
    secp256k1_u128_mul(&c, a4, b[4]);
    /* [c 0 0 0 0 d 0 0 0] = [p8 0 0 0 0 p3 0 0 0] */
    secp256k1_u128_accum_mul(&d, R, secp256k1_u128_to_u64(&c)); secp256k1_u128_rshift(&c, 64);
    /* [(c<<12) 0 0 0 0 0 d 0 0 0] = [p8 0 0 0 0 p3 0 0 0] */
    t3 = secp256k1_u128_to_u64(&d) & M; secp256k1_u128_rshift(&d, 52);
    /* [(c<<12) 0 0 0 0 d t3 0 0 0] = [p8 0 0 0 0 p3 0 0 0] */

    secp256k1_u128_accum_mul(&d, a0, b[4]);
    secp256k1_u128_accum_mul(&d, a1, b[3]);
    secp256k1_u128_accum_mul(&d, a2, b[2]);
    secp256k1_u128_accum_mul(&d, a3, b[1]);
    secp256k1_u128_accum_mul(&d, a4, b[0]);
    /* [(c<<12) 0 0 0 0 d t3 0 0 0] = [p8 0 0 0 p4 p3 0 0 0] */
    secp256k1_u128_accum_mul(&d, R << 12, secp256k1_u128_to_u64(&c));
    /* [d t3 0 0 0] = [p8 0 0 0 p4 p3 0 0 0] */
    t4 = secp256k1_u128_to_u64(&d) & M; secp256k1_u128_rshift(&d, 52);
    /* [d t4 t3 0 0 0] = [p8 0 0 0 p4 p3 0 0 0] */
    tx = (t4 >> 48); t4 &= (M >> 4);
    /* [d t4+(tx<<48) t3 0 0 0] = [p8 0 0 0 p4 p3 0 0 0] */

    secp256k1_u128_mul(&c, a0, b[0]);
    /* [d t4+(tx<<48) t3 0 0 c] = [p8 0 0 0 p4 p3 0 0 p0] */
    secp256k1_u128_accum_mul(&d, a1, b[4]);
    secp256k1_u128_accum_mul(&d, a2, b[3]);
    secp256k1_u128_accum_mul(&d, a3, b[2]);
    secp256k1_u128_accum_mul(&d, a4, b[1]);
    /* [d t4+(tx<<48) t3 0 0 c] = [p8 0 0 p5 p4 p3 0 0 p0] */
    u0 = secp256k1_u128_to_u64(&d) & M; secp256k1_u128_rshift(&d, 52);
    /* [d u0 t4+(tx<<48) t3 0 0 c] = [p8 0 0 p5 p4 p3 0 0 p0] */
    /* [d 0 t4+(tx<<48)+(u0<<52) t3 0 0 c] = [p8 0 0 p5 p4 p3 0 0 p0] */
    u0 = (u0 << 4) | tx;
    /* [d 0 t4+(u0<<48) t3 0 0 c] = [p8 0 0 p5 p4 p3 0 0 p0] */
    secp256k1_u128_accum_mul(&c, u0, R >> 4);
    /* [d 0 t4 t3 0 0 c] = [p8 0 0 p5 p4 p3 0 0 p0] */
    r[0] = secp256k1_u128_to_u64(&c) & M; secp256k1_u128_rshift(&c, 52);
    /* [d 0 t4 t3 0 c r0] = [p8 0 0 p5 p4 p3 0 0 p0] */

    secp256k1_u128_accum_mul(&c, a0, b[1]);
    secp256k1_u128_accum_mul(&c, a1, b[0]);
    /* [d 0 t4 t3 0 c r0] = [p8 0 0 p5 p4 p3 0 p1 p0] */
    secp256k1_u128_accum_mul(&d, a2, b[4]);
    secp256k1_u128_accum_mul(&d, a3, b[3]);
    secp256k1_u128_accum_mul(&d, a4, b[2]);
    /* [d 0 t4 t3 0 c r0] = [p8 0 p6 p5 p4 p3 0 p1 p0] */
    secp256k1_u128_accum_mul(&c, secp256k1_u128_to_u64(&d) & M, R); secp256k1_u128_rshift(&d, 52);
    /* [d 0 0 t4 t3 0 c r0] = [p8 0 p6 p5 p4 p3 0 p1 p0] */
    r[1] = secp256k1_u128_to_u64(&c) & M; secp256k1_u128_rshift(&c, 52);
    /* [d 0 0 t4 t3 c r1 r0] = [p8 0 p6 p5 p4 p3 0 p1 p0] */

    secp256k1_u128_accum_mul(&c, a0, b[2]);
    secp256k1_u128_accum_mul(&c, a1, b[1]);
    secp256k1_u128_accum_mul(&c, a2, b[0]);
    /* [d 0 0 t4 t3 c r1 r0] = [p8 0 p6 p5 p4 p3 p2 p1 p0] */
    secp256k1_u128_accum_mul(&d, a3, b[4]);
    secp256k1_u128_accum_mul(&d, a4, b[3]);
    /* [d 0 0 t4 t3 c t1 r0] = [p8 p7 p6 p5 p4 p3 p2 p1 p0] */
    secp256k1_u128_accum_mul(&c, R, secp256k1_u128_to_u64(&d)); secp256k1_u128_rshift(&d, 64);
    /* [(d<<12) 0 0 0 t4 t3 c r1 r0] = [p8 p7 p6 p5 p4 p3 p2 p1 p0] */

    r[2] = secp256k1_u128_to_u64(&c) & M; secp256k1_u128_rshift(&c, 52);
    /* [(d<<12) 0 0 0 t4 t3+c r2 r1 r0] = [p8 p7 p6 p5 p4 p3 p2 p1 p0] */
    secp256k1_u128_accum_mul(&c, R << 12, secp256k1_u128_to_u64(&d));
    secp256k1_u128_accum_u64(&c, t3);
    /* [t4 c r2 r1 r0] = [p8 p7 p6 p5 p4 p3 p2 p1 p0] */
    r[3] = secp256k1_u128_to_u64(&c) & M; secp256k1_u128_rshift(&c, 52);
    /* [t4+c r3 r2 r1 r0] = [p8 p7 p6 p5 p4 p3 p2 p1 p0] */
    r[4] = secp256k1_u128_to_u64(&c) + t4;
    /* [r4 r3 r2 r1 r0] = [p8 p7 p6 p5 p4 p3 p2 p1 p0] */
}
static void secp256k1_fe_mul(secp256k1_fe *r, const secp256k1_fe *a, const secp256k1_fe *b) {
    secp256k1_fe_mul_inner(r->n, a->n, b->n);
}
static void secp256k1_fe_mul_inner_const(ulong *r, const ulong *a, __constant const ulong *b) {
    secp256k1_uint128 c, d;
    ulong t3, t4, tx, u0;
    ulong a0 = a[0], a1 = a[1], a2 = a[2], a3 = a[3], a4 = a[4];
    const ulong M = 0xFFFFFFFFFFFFFUL, R = 0x1000003D10UL;

    /*  [... a b c] is a shorthand for ... + a<<104 + b<<52 + c<<0 mod n.
     *  for 0 <= x <= 4, px is a shorthand for sum(a[i]*b[x-i], i=0..x).
     *  for 4 <= x <= 8, px is a shorthand for sum(a[i]*b[x-i], i=(x-4)..4)
     *  Note that [x 0 0 0 0 0] = [x*R].
     */

    secp256k1_u128_mul(&d, a0, b[3]);
    secp256k1_u128_accum_mul(&d, a1, b[2]);
    secp256k1_u128_accum_mul(&d, a2, b[1]);
    secp256k1_u128_accum_mul(&d, a3, b[0]);
    /* [d 0 0 0] = [p3 0 0 0] */
    secp256k1_u128_mul(&c, a4, b[4]);
    /* [c 0 0 0 0 d 0 0 0] = [p8 0 0 0 0 p3 0 0 0] */
    secp256k1_u128_accum_mul(&d, R, secp256k1_u128_to_u64(&c)); secp256k1_u128_rshift(&c, 64);
    /* [(c<<12) 0 0 0 0 0 d 0 0 0] = [p8 0 0 0 0 p3 0 0 0] */
    t3 = secp256k1_u128_to_u64(&d) & M; secp256k1_u128_rshift(&d, 52);
    /* [(c<<12) 0 0 0 0 d t3 0 0 0] = [p8 0 0 0 0 p3 0 0 0] */

    secp256k1_u128_accum_mul(&d, a0, b[4]);
    secp256k1_u128_accum_mul(&d, a1, b[3]);
    secp256k1_u128_accum_mul(&d, a2, b[2]);
    secp256k1_u128_accum_mul(&d, a3, b[1]);
    secp256k1_u128_accum_mul(&d, a4, b[0]);
    /* [(c<<12) 0 0 0 0 d t3 0 0 0] = [p8 0 0 0 p4 p3 0 0 0] */
    secp256k1_u128_accum_mul(&d, R << 12, secp256k1_u128_to_u64(&c));
    /* [d t3 0 0 0] = [p8 0 0 0 p4 p3 0 0 0] */
    t4 = secp256k1_u128_to_u64(&d) & M; secp256k1_u128_rshift(&d, 52);
    /* [d t4 t3 0 0 0] = [p8 0 0 0 p4 p3 0 0 0] */
    tx = (t4 >> 48); t4 &= (M >> 4);
    /* [d t4+(tx<<48) t3 0 0 0] = [p8 0 0 0 p4 p3 0 0 0] */

    secp256k1_u128_mul(&c, a0, b[0]);
    /* [d t4+(tx<<48) t3 0 0 c] = [p8 0 0 0 p4 p3 0 0 p0] */
    secp256k1_u128_accum_mul(&d, a1, b[4]);
    secp256k1_u128_accum_mul(&d, a2, b[3]);
    secp256k1_u128_accum_mul(&d, a3, b[2]);
    secp256k1_u128_accum_mul(&d, a4, b[1]);
    /* [d t4+(tx<<48) t3 0 0 c] = [p8 0 0 p5 p4 p3 0 0 p0] */
    u0 = secp256k1_u128_to_u64(&d) & M; secp256k1_u128_rshift(&d, 52);
    /* [d u0 t4+(tx<<48) t3 0 0 c] = [p8 0 0 p5 p4 p3 0 0 p0] */
    /* [d 0 t4+(tx<<48)+(u0<<52) t3 0 0 c] = [p8 0 0 p5 p4 p3 0 0 p0] */
    u0 = (u0 << 4) | tx;
    /* [d 0 t4+(u0<<48) t3 0 0 c] = [p8 0 0 p5 p4 p3 0 0 p0] */
    secp256k1_u128_accum_mul(&c, u0, R >> 4);
    /* [d 0 t4 t3 0 0 c] = [p8 0 0 p5 p4 p3 0 0 p0] */
    r[0] = secp256k1_u128_to_u64(&c) & M; secp256k1_u128_rshift(&c, 52);
    /* [d 0 t4 t3 0 c r0] = [p8 0 0 p5 p4 p3 0 0 p0] */

    secp256k1_u128_accum_mul(&c, a0, b[1]);
    secp256k1_u128_accum_mul(&c, a1, b[0]);
    /* [d 0 t4 t3 0 c r0] = [p8 0 0 p5 p4 p3 0 p1 p0] */
    secp256k1_u128_accum_mul(&d, a2, b[4]);
    secp256k1_u128_accum_mul(&d, a3, b[3]);
    secp256k1_u128_accum_mul(&d, a4, b[2]);
    /* [d 0 t4 t3 0 c r0] = [p8 0 p6 p5 p4 p3 0 p1 p0] */
    secp256k1_u128_accum_mul(&c, secp256k1_u128_to_u64(&d) & M, R); secp256k1_u128_rshift(&d, 52);
    /* [d 0 0 t4 t3 0 c r0] = [p8 0 p6 p5 p4 p3 0 p1 p0] */
    r[1] = secp256k1_u128_to_u64(&c) & M; secp256k1_u128_rshift(&c, 52);
    /* [d 0 0 t4 t3 c r1 r0] = [p8 0 p6 p5 p4 p3 0 p1 p0] */

    secp256k1_u128_accum_mul(&c, a0, b[2]);
    secp256k1_u128_accum_mul(&c, a1, b[1]);
    secp256k1_u128_accum_mul(&c, a2, b[0]);
    /* [d 0 0 t4 t3 c r1 r0] = [p8 0 p6 p5 p4 p3 p2 p1 p0] */
    secp256k1_u128_accum_mul(&d, a3, b[4]);
    secp256k1_u128_accum_mul(&d, a4, b[3]);
    /* [d 0 0 t4 t3 c t1 r0] = [p8 p7 p6 p5 p4 p3 p2 p1 p0] */
    secp256k1_u128_accum_mul(&c, R, secp256k1_u128_to_u64(&d)); secp256k1_u128_rshift(&d, 64);
    /* [(d<<12) 0 0 0 t4 t3 c r1 r0] = [p8 p7 p6 p5 p4 p3 p2 p1 p0] */

    r[2] = secp256k1_u128_to_u64(&c) & M; secp256k1_u128_rshift(&c, 52);
    /* [(d<<12) 0 0 0 t4 t3+c r2 r1 r0] = [p8 p7 p6 p5 p4 p3 p2 p1 p0] */
    secp256k1_u128_accum_mul(&c, R << 12, secp256k1_u128_to_u64(&d));
    secp256k1_u128_accum_u64(&c, t3);
    /* [t4 c r2 r1 r0] = [p8 p7 p6 p5 p4 p3 p2 p1 p0] */
    r[3] = secp256k1_u128_to_u64(&c) & M; secp256k1_u128_rshift(&c, 52);
    /* [t4+c r3 r2 r1 r0] = [p8 p7 p6 p5 p4 p3 p2 p1 p0] */
    r[4] = secp256k1_u128_to_u64(&c) + t4;
    /* [r4 r3 r2 r1 r0] = [p8 p7 p6 p5 p4 p3 p2 p1 p0] */
}
static void secp256k1_fe_mul_const(secp256k1_fe *r, const secp256k1_fe *a, __constant const secp256k1_fe *b) {
    secp256k1_fe_mul_inner_const(r->n, a->n, b->n);
}
static void secp256k1_fe_mul_int(secp256k1_fe *r, int a) {
    r->n[0] *= a;
    r->n[1] *= a;
    r->n[2] *= a;
    r->n[3] *= a;
    r->n[4] *= a;
}
static void secp256k1_fe_normalize_weak(secp256k1_fe *r) {
    ulong t0 = r->n[0], t1 = r->n[1], t2 = r->n[2], t3 = r->n[3], t4 = r->n[4];

    /* Reduce t4 at the start so there will be at most a single carry from the first pass */
    ulong x = t4>>48; t4 &= 0x0FFFFFFFFFFFFUL;

    /* The first pass ensures the magnitude is 1, ... */
    t0 += x * 0x1000003D1ULL;
    t1 += (t0 >> 52); t0 &= 0xFFFFFFFFFFFFFUL;
    t2 += (t1 >> 52); t1 &= 0xFFFFFFFFFFFFFUL;
    t3 += (t2 >> 52); t2 &= 0xFFFFFFFFFFFFFUL;
    t4 += (t3 >> 52); t3 &= 0xFFFFFFFFFFFFFUL;

    r->n[0] = t0; r->n[1] = t1; r->n[2] = t2; r->n[3] = t3; r->n[4] = t4;
}
static int secp256k1_fe_normalizes_to_zero_var(const secp256k1_fe *r) {
    ulong t0, t1, t2, t3, t4;
    ulong z0, z1;
    ulong x;

    t0 = r->n[0];
    t4 = r->n[4];

    /* Reduce t4 at the start so there will be at most a single carry from the first pass */
    x = t4 >> 48;

    /* The first pass ensures the magnitude is 1, ... */
    t0 += x * 0x1000003D1UL;

    /* z0 tracks a possible raw value of 0, z1 tracks a possible raw value of P */
    z0 = t0 & 0xFFFFFFFFFFFFFUL;
    z1 = z0 ^ 0x1000003D0UL;

    /* Fast return path should catch the majority of cases */
    if ((z0 != 0ULL) & (z1 != 0xFFFFFFFFFFFFFUL)) {
        return 0;
    }

    t1 = r->n[1];
    t2 = r->n[2];
    t3 = r->n[3];

    t4 &= 0x0FFFFFFFFFFFFUL;

    t1 += (t0 >> 52);
    t2 += (t1 >> 52); t1 &= 0xFFFFFFFFFFFFFUL; z0 |= t1; z1 &= t1;
    t3 += (t2 >> 52); t2 &= 0xFFFFFFFFFFFFFUL; z0 |= t2; z1 &= t2;
    t4 += (t3 >> 52); t3 &= 0xFFFFFFFFFFFFFUL; z0 |= t3; z1 &= t3;
                                                z0 |= t4; z1 &= t4 ^ 0xF000000000000UL;

    return (z0 == 0) | (z1 == 0xFFFFFFFFFFFFFUL);
}
static void secp256k1_fe_half(secp256k1_fe *r) {
    ulong t0 = r->n[0], t1 = r->n[1], t2 = r->n[2], t3 = r->n[3], t4 = r->n[4];
    ulong one = (ulong)1;
    ulong mask = -(t0 & one) >> 12;

    /* Bounds analysis (over the rationals).
     *
     * Let m = r->magnitude
     *     C = 0xFFFFFFFFFFFFFULL * 2
     *     D = 0x0FFFFFFFFFFFFULL * 2
     *
     * Initial bounds: t0..t3 <= C * m
     *                     t4 <= D * m
     */

    t0 += 0xFFFFEFFFFFC2FUL & mask;
    t1 += mask;
    t2 += mask;
    t3 += mask;
    t4 += mask >> 4;

    /* t0..t3: added <= C/2
     *     t4: added <= D/2
     *
     * Current bounds: t0..t3 <= C * (m + 1/2)
     *                     t4 <= D * (m + 1/2)
     */

    r->n[0] = (t0 >> 1) + ((t1 & one) << 51);
    r->n[1] = (t1 >> 1) + ((t2 & one) << 51);
    r->n[2] = (t2 >> 1) + ((t3 & one) << 51);
    r->n[3] = (t3 >> 1) + ((t4 & one) << 51);
    r->n[4] = (t4 >> 1);

    /* t0..t3: shifted right and added <= C/4 + 1/2
     *     t4: shifted right
     *
     * Current bounds: t0..t3 <= C * (m/2 + 1/2)
     *                     t4 <= D * (m/2 + 1/4)
     *
     * Therefore the output magnitude (M) has to be set such that:
     *     t0..t3: C * M >= C * (m/2 + 1/2)
     *         t4: D * M >= D * (m/2 + 1/4)
     *
     * It suffices for all limbs that, for any input magnitude m:
     *     M >= m/2 + 1/2
     *
     * and since we want the smallest such integer value for M:
     *     M == floor(m/2) + 1
     */
}
static void secp256k1_fe_negate(secp256k1_fe *r, const secp256k1_fe *a, int m) {
    /* Due to the properties above, the left hand in the subtractions below is never less than
     * the right hand. */
    r->n[0] = 0xFFFFEFFFFFC2FUL * 2 * (m + 1) - a->n[0];
    r->n[1] = 0xFFFFFFFFFFFFFUL * 2 * (m + 1) - a->n[1];
    r->n[2] = 0xFFFFFFFFFFFFFUL * 2 * (m + 1) - a->n[2];
    r->n[3] = 0xFFFFFFFFFFFFFUL * 2 * (m + 1) - a->n[3];
    r->n[4] = 0x0FFFFFFFFFFFFUL * 2 * (m + 1) - a->n[4];
}
static int secp256k1_fe_equal_var(const secp256k1_fe *a, const secp256k1_fe *b) {
    secp256k1_fe na;
    secp256k1_fe_negate(&na, a, 1);
    secp256k1_fe_add(&na, b);
    return secp256k1_fe_normalizes_to_zero_var(&na);
}
static int secp256k1_fe_cmp_var(const secp256k1_fe *a, const secp256k1_fe *b) {
    int i;
    for (i = 4; i >= 0; i--) {
        if (a->n[i] > b->n[i]) {
            return 1;
        }
        if (a->n[i] < b->n[i]) {
            return -1;
        }
    }
    return 0;
}
static int secp256k1_fe_cmp_var_const(const secp256k1_fe *a, __constant const secp256k1_fe *b) {
    int i;
    for (i = 4; i >= 0; i--) {
        if (a->n[i] > b->n[i]) {
            return 1;
        }
        if (a->n[i] < b->n[i]) {
            return -1;
        }
    }
    return 0;
}
static void secp256k1_ge_set_xy(secp256k1_ge *r, const secp256k1_fe *x, const secp256k1_fe *y) {
    r->infinity = 0;
    r->x = *x;
    r->y = *y;
}
static void secp256k1_ge_from_storage(secp256k1_ge *r, const secp256k1_ge_storage *a) {
    secp256k1_fe_from_storage(&r->x, &a->x);
    secp256k1_fe_from_storage(&r->y, &a->y);
    r->infinity = 0;
}
static void secp256k1_ge_from_storage_const(secp256k1_ge *r, __constant const secp256k1_ge_storage *a) {
    secp256k1_fe_from_storage_const(&r->x, &a->x);
    secp256k1_fe_from_storage_const(&r->y, &a->y);
    r->infinity = 0;
}
static void secp256k1_ge_set_ge_zinv(secp256k1_ge *r, const secp256k1_ge *a, const secp256k1_fe *zi) {
    secp256k1_fe zi2;
    secp256k1_fe zi3;
    secp256k1_fe_sqr(&zi2, zi);
    secp256k1_fe_mul(&zi3, &zi2, zi);
    secp256k1_fe_mul(&r->x, &a->x, &zi2);
    secp256k1_fe_mul(&r->y, &a->y, &zi3);
    r->infinity = a->infinity;
}
static void secp256k1_ge_set_gej_zinv(secp256k1_ge *r, const secp256k1_gej *a, const secp256k1_fe *zi) {
    secp256k1_fe zi2;
    secp256k1_fe zi3;
    secp256k1_fe_sqr(&zi2, zi);
    secp256k1_fe_mul(&zi3, &zi2, zi);
    secp256k1_fe_mul(&r->x, &a->x, &zi2);
    secp256k1_fe_mul(&r->y, &a->y, &zi3);
    r->infinity = a->infinity;
}
static void secp256k1_ge_table_set_globalz(ulong len, secp256k1_ge *a, const secp256k1_fe *zr) {
    ulong i = len - 1;
    secp256k1_fe zs;

    if (len > 0) {
        /* Ensure all y values are in weak normal form for fast negation of points */
        secp256k1_fe_normalize_weak(&a[i].y);
        zs = zr[i];

        /* Work our way backwards, using the z-ratios to scale the x/y values. */
        while (i > 0) {
            if (i != len - 1) {
                secp256k1_fe_mul(&zs, &zs, &zr[i]);
            }
            i--;
            secp256k1_ge_set_ge_zinv(&a[i], &a[i], &zs);
        }
    }
}
static int secp256k1_gej_is_infinity(const secp256k1_gej *a) {
    return a->infinity;
}
static void secp256k1_gej_set_ge(secp256k1_gej *r, const secp256k1_ge *a) {
   r->infinity = a->infinity;
   r->x = a->x;
   r->y = a->y;
   secp256k1_fe_set_int(&r->z, 1);
}
static void secp256k1_gej_set_infinity(secp256k1_gej *r) {
    r->infinity = 1;
    secp256k1_fe_clear(&r->x);
    secp256k1_fe_clear(&r->y);
    secp256k1_fe_clear(&r->z);
}
static void secp256k1_gej_rescale(secp256k1_gej *r, const secp256k1_fe *s) {
    // Operations: 4 mul, 1 sqr
    secp256k1_fe zz;
    secp256k1_fe_sqr(&zz, s);
    secp256k1_fe_mul(&r->x, &r->x, &zz);  // r->x *= s^2
    secp256k1_fe_mul(&r->y, &r->y, &zz);
    secp256k1_fe_mul(&r->y, &r->y, s);    // r->y *= s^3
    secp256k1_fe_mul(&r->z, &r->z, s);    // r->z *= s
}
static void secp256k1_gej_double(secp256k1_gej *r, const secp256k1_gej *a) {
    /* Operations: 3 mul, 4 sqr, 8 add/half/mul_int/negate */
    secp256k1_fe l, s, t;

    r->infinity = a->infinity;

    /* Formula used:
     * L = (3/2) * X1^2
     * S = Y1^2
     * T = -X1*S
     * X3 = L^2 + 2*T
     * Y3 = -(L*(X3 + T) + S^2)
     * Z3 = Y1*Z1
     */

    secp256k1_fe_mul(&r->z, &a->z, &a->y); /* Z3 = Y1*Z1 (1) */
    secp256k1_fe_sqr(&s, &a->y);           /* S = Y1^2 (1) */
    secp256k1_fe_sqr(&l, &a->x);           /* L = X1^2 (1) */
    secp256k1_fe_mul_int(&l, 3);           /* L = 3*X1^2 (3) */
    secp256k1_fe_half(&l);                 /* L = 3/2*X1^2 (2) */
    secp256k1_fe_negate(&t, &s, 1);        /* T = -S (2) */
    secp256k1_fe_mul(&t, &t, &a->x);       /* T = -X1*S (1) */
    secp256k1_fe_sqr(&r->x, &l);           /* X3 = L^2 (1) */
    secp256k1_fe_add(&r->x, &t);           /* X3 = L^2 + T (2) */
    secp256k1_fe_add(&r->x, &t);           /* X3 = L^2 + 2*T (3) */
    secp256k1_fe_sqr(&s, &s);              /* S' = S^2 (1) */
    secp256k1_fe_add(&t, &r->x);           /* T' = X3 + T (4) */
    secp256k1_fe_mul(&r->y, &t, &l);       /* Y3 = L*(X3 + T) (1) */
    secp256k1_fe_add(&r->y, &s);           /* Y3 = L*(X3 + T) + S^2 (2) */
    secp256k1_fe_negate(&r->y, &r->y, 2);  /* Y3 = -(L*(X3 + T) + S^2) (3) */
}
static void secp256k1_gej_double_var(secp256k1_gej *r, const secp256k1_gej *a, secp256k1_fe *rzr) {
    /** For secp256k1, 2Q is infinity if and only if Q is infinity. This is because if 2Q = infinity,
     *  Q must equal -Q, or that Q.y == -(Q.y), or Q.y is 0. For a point on y^2 = x^3 + 7 to have
     *  y=0, x^3 must be -7 mod p. However, -7 has no cube root mod p.
     *
     *  Having said this, if this function receives a point on a sextic twist, e.g. by
     *  a fault attack, it is possible for y to be 0. This happens for y^2 = x^3 + 6,
     *  since -6 does have a cube root mod p. For this point, this function will not set
     *  the infinity flag even though the point doubles to infinity, and the result
     *  point will be gibberish (z = 0 but infinity = 0).
     */
    if (a->infinity) {
        secp256k1_gej_set_infinity(r);
        if (rzr != 0) {
            secp256k1_fe_set_int(rzr, 1);
        }
        return;
    }

    if (rzr != 0) {
        *rzr = a->y;
        secp256k1_fe_normalize_weak(rzr);
    }

    secp256k1_gej_double(r, a);
}
static void secp256k1_gej_add_ge_var(secp256k1_gej *r, const secp256k1_gej *a, const secp256k1_ge *b, secp256k1_fe *rzr) {
    /* 8 mul, 3 sqr, 13 add/negate/normalize_weak/normalizes_to_zero (ignoring special cases) */
    secp256k1_fe z12, u1, u2, s1, s2, h, i, h2, h3, t;

    if (a->infinity) {
        secp256k1_gej_set_ge(r, b);
        return;
    }
    if (b->infinity) {
        if (rzr != 0) {
            secp256k1_fe_set_int(rzr, 1);
        }
        *r = *a;
        return;
    }

    secp256k1_fe_sqr(&z12, &a->z);
    u1 = a->x; secp256k1_fe_normalize_weak(&u1);
    secp256k1_fe_mul(&u2, &b->x, &z12);
    s1 = a->y; secp256k1_fe_normalize_weak(&s1);
    secp256k1_fe_mul(&s2, &b->y, &z12); secp256k1_fe_mul(&s2, &s2, &a->z);
    secp256k1_fe_negate(&h, &u1, 1); secp256k1_fe_add(&h, &u2);
    secp256k1_fe_negate(&i, &s2, 1); secp256k1_fe_add(&i, &s1);
    if (secp256k1_fe_normalizes_to_zero_var(&h)) {
        if (secp256k1_fe_normalizes_to_zero_var(&i)) {
            secp256k1_gej_double_var(r, a, rzr);
        } else {
            if (rzr != 0) {
                secp256k1_fe_set_int(rzr, 0);
            }
            secp256k1_gej_set_infinity(r);
        }
        return;
    }

    r->infinity = 0;
    if (rzr != 0) {
        *rzr = h;
    }
    secp256k1_fe_mul(&r->z, &a->z, &h);

    secp256k1_fe_sqr(&h2, &h);
    secp256k1_fe_negate(&h2, &h2, 1);
    secp256k1_fe_mul(&h3, &h2, &h);
    secp256k1_fe_mul(&t, &u1, &h2);

    secp256k1_fe_sqr(&r->x, &i);
    secp256k1_fe_add(&r->x, &h3);
    secp256k1_fe_add(&r->x, &t);
    secp256k1_fe_add(&r->x, &t);

    secp256k1_fe_add(&t, &r->x);
    secp256k1_fe_mul(&r->y, &t, &i);
    secp256k1_fe_mul(&h3, &h3, &s1);
    secp256k1_fe_add(&r->y, &h3);
}
static void secp256k1_gej_add_zinv_var(secp256k1_gej *r, const secp256k1_gej *a, const secp256k1_ge *b, const secp256k1_fe *bzinv) {
    /* 9 mul, 3 sqr, 13 add/negate/normalize_weak/normalizes_to_zero (ignoring special cases) */
    secp256k1_fe az, z12, u1, u2, s1, s2, h, i, h2, h3, t;

    if (a->infinity) {
        secp256k1_fe bzinv2, bzinv3;
        r->infinity = b->infinity;
        secp256k1_fe_sqr(&bzinv2, bzinv);
        secp256k1_fe_mul(&bzinv3, &bzinv2, bzinv);
        secp256k1_fe_mul(&r->x, &b->x, &bzinv2);
        secp256k1_fe_mul(&r->y, &b->y, &bzinv3);
        secp256k1_fe_set_int(&r->z, 1);
        return;
    }
    if (b->infinity) {
        *r = *a;
        return;
    }

    /** We need to calculate (rx,ry,rz) = (ax,ay,az) + (bx,by,1/bzinv). Due to
     *  secp256k1's isomorphism we can multiply the Z coordinates on both sides
     *  by bzinv, and get: (rx,ry,rz*bzinv) = (ax,ay,az*bzinv) + (bx,by,1).
     *  This means that (rx,ry,rz) can be calculated as
     *  (ax,ay,az*bzinv) + (bx,by,1), when not applying the bzinv factor to rz.
     *  The variable az below holds the modified Z coordinate for a, which is used
     *  for the computation of rx and ry, but not for rz.
     */
    secp256k1_fe_mul(&az, &a->z, bzinv);

    secp256k1_fe_sqr(&z12, &az);
    u1 = a->x; secp256k1_fe_normalize_weak(&u1);
    secp256k1_fe_mul(&u2, &b->x, &z12);
    s1 = a->y; secp256k1_fe_normalize_weak(&s1);
    secp256k1_fe_mul(&s2, &b->y, &z12); secp256k1_fe_mul(&s2, &s2, &az);
    secp256k1_fe_negate(&h, &u1, 1); secp256k1_fe_add(&h, &u2);
    secp256k1_fe_negate(&i, &s2, 1); secp256k1_fe_add(&i, &s1);
    if (secp256k1_fe_normalizes_to_zero_var(&h)) {
        if (secp256k1_fe_normalizes_to_zero_var(&i)) {
            secp256k1_gej_double_var(r, a, 0);
        } else {
            secp256k1_gej_set_infinity(r);
        }
        return;
    }

    r->infinity = 0;
    secp256k1_fe_mul(&r->z, &a->z, &h);

    secp256k1_fe_sqr(&h2, &h);
    secp256k1_fe_negate(&h2, &h2, 1);
    secp256k1_fe_mul(&h3, &h2, &h);
    secp256k1_fe_mul(&t, &u1, &h2);

    secp256k1_fe_sqr(&r->x, &i);
    secp256k1_fe_add(&r->x, &h3);
    secp256k1_fe_add(&r->x, &t);
    secp256k1_fe_add(&r->x, &t);

    secp256k1_fe_add(&t, &r->x);
    secp256k1_fe_mul(&r->y, &t, &i);
    secp256k1_fe_mul(&h3, &h3, &s1);
    secp256k1_fe_add(&r->y, &h3);
}
static int secp256k1_gej_eq_x_var(const secp256k1_fe *x, const secp256k1_gej *a) {
    secp256k1_fe r, r2;
    secp256k1_fe_sqr(&r, &a->z); secp256k1_fe_mul(&r, &r, x);
    r2 = a->x; secp256k1_fe_normalize_weak(&r2);
    return secp256k1_fe_equal_var(&r, &r2);
}

/** Mathmatical functions for secp256k1_scalar_mul_512 and secp256k1_scalar_reduce_512. */
static void muladd_fast(ulong a, ulong b, ulong *c0, ulong *c1) {
	secp256k1_uint128 t;
	secp256k1_u128_mul(&t, a, b);
	*c0 += t.lo;           /* overflow is handled on the next line */
	t.hi += (*c0 < t.lo);  /* at most 0xFFFFFFFFFFFFFFFF */
    *c1 += t.hi;           /* never overflows by contract */
}
static void muladd(ulong a, ulong b, ulong *c0, ulong *c1, uint *c2) {
	secp256k1_uint128 t;
	secp256k1_u128_mul(&t, a, b);
	*c0 += t.lo;           // overflow is handled on the next line
	t.hi += (*c0 < t.lo);  // at most 0xFFFFFFFFFFFFFFFF
	*c1 += t.hi;           // overflow is handled on the next line
	*c2 += (*c1 < t.hi);   // never overflows by contract
}
static void muladd_ulong(ulong a, ulong b, ulong *c0, ulong *c1, ulong *c2) {
	secp256k1_uint128 t;
	secp256k1_u128_mul(&t, a, b);
	*c0 += t.lo;           // overflow is handled on the next line
	t.hi += (*c0 < t.lo);  // at most 0xFFFFFFFFFFFFFFFF
	*c1 += t.hi;           // overflow is handled on the next line
	*c2 += (*c1 < t.hi);   // never overflows by contract
}
static void extract_fast(ulong *n, ulong *c0, ulong *c1) {
	*n = *c0;
    *c0 = *c1;
    *c1 = 0;
}
static void extract(ulong *n, ulong *c0, ulong *c1, uint *c2) {
	*n = *c0;
    *c0 = *c1;
    *c1 = *c2;
    *c2 = 0;
}
static void extract_ulong(ulong *n, ulong *c0, ulong *c1, ulong *c2) {
	*n = *c0;
    *c0 = *c1;
    *c1 = *c2;
    *c2 = 0;
}
static void sumadd(ulong a, ulong *c0, ulong *c1, ulong *c2) { \
    uint over;
    *c0 += (a);            // overflow is handled on the next line
    over = (*c0 < (a));
    *c1 += over;           // overflow is handled on the next line
    *c2 += (*c1 < over);   // never overflows by contract
}
static void sumadd_fast(ulong a, ulong *c0, ulong *c1) {
    *c0 += (a);            // overflow is handled on the next line
    *c1 += (*c0 < (a));    // never overflows by contract (verified the next line)
}

/** A scalar modulo the group order of the secp256k1 curve. */
typedef struct { ulong d[4]; } secp256k1_scalar;
__constant secp256k1_scalar const_minus_b1 = {{ 0x6F547FA90ABFE4C3UL, 0xE4437ED6010E8828UL, 0x0000000000000000UL, 0x0000000000000000UL }};
__constant secp256k1_scalar const_minus_b2 = {{ 0xFFFFFFFFFFFFFFFFUL, 0xFFFFFFFFFFFFFFFFUL, 0x8A280AC50774346DUL, 0xD765CDA83DB1562CUL }};
__constant secp256k1_scalar const_g1       = {{ 0x3086D221A7D46BCDUL, 0xE86C90E49284EB15UL, 0x3DAA8A1471E8CA7FUL, 0xE893209A45DBB031UL }};
__constant secp256k1_scalar const_g2       = {{ 0xE4437ED6010E8828UL, 0x6F547FA90ABFE4C4UL, 0x221208AC9DF506C6UL, 0x1571B4AE8AC47F71UL }};
__constant secp256k1_scalar const_lambda   = {{ 0x5363AD4CC05C30E0UL, 0xA5261C028812645AUL, 0x122E22EA20816678UL, 0xDF02967C1B23BD72UL }};
static int secp256k1_scalar_check_overflow(const secp256k1_scalar *a) {
    int yes = 0;
    int no = 0;
    no |= (a->d[3] < SECP256K1_N_3); /* No need for a > check. */
    no |= (a->d[2] < SECP256K1_N_2);
    yes |= (a->d[2] > SECP256K1_N_2) & ~no;
    no |= (a->d[1] < SECP256K1_N_1);
    yes |= (a->d[1] > SECP256K1_N_1) & ~no;
    yes |= (a->d[0] >= SECP256K1_N_0) & ~no;
    return yes;
}
static int secp256k1_scalar_is_high(const secp256k1_scalar *a) {
    int yes = 0;
    int no = 0;
    no |= (a->d[3] < SECP256K1_N_H_3);
    yes |= (a->d[3] > SECP256K1_N_H_3) & ~no;
    no |= (a->d[2] < SECP256K1_N_H_2) & ~yes; /* No need for a > check. */
    no |= (a->d[1] < SECP256K1_N_H_1) & ~yes;
    yes |= (a->d[1] > SECP256K1_N_H_1) & ~no;
    yes |= (a->d[0] > SECP256K1_N_H_0) & ~no;
    return yes;
}
static int secp256k1_scalar_is_zero(const secp256k1_scalar *a) {
    return (a->d[0] | a->d[1] | a->d[2] | a->d[3]) == 0;
}
// NEEDS TESTING - Redo this garbage
static int secp256k1_scalar_reduce(secp256k1_scalar *r, unsigned int overflow) {
    secp256k1_uint128 t;

    //secp256k1_u128_from_u64(&t, r->d[0]);
	t.lo = r->d[0];
    
	//secp256k1_u128_accum_u64(&t, overflow * SECP256K1_N_C_0);
	secp256k1_u128_accum_u64(&t, overflow * SECP256K1_N_C_0);
 
	//r->d[0] = secp256k1_u128_to_u64(&t);
	r->d[0] = t.lo;
	
	//secp256k1_u128_rshift(&t, 64);
    t.lo = t.hi;
	t.hi = 0;
	
	//secp256k1_u128_accum_u64(&t, r->d[1]);
	secp256k1_u128_accum_u64(&t, r->d[1]);

    //secp256k1_u128_accum_u64(&t, overflow * SECP256K1_N_C_1);
	secp256k1_u128_accum_u64(&t, overflow * SECP256K1_N_C_1);
    
	//r->d[1] = secp256k1_u128_to_u64(&t);
	r->d[1] = t.lo;

	// secp256k1_u128_rshift(&t, 64);
	t.lo = t.hi;
	t.hi = 0;

    //secp256k1_u128_accum_u64(&t, r->d[2]);
	secp256k1_u128_accum_u64(&t, r->d[2]);

    //secp256k1_u128_accum_u64(&t, overflow * SECP256K1_N_C_2);
	secp256k1_u128_accum_u64(&t, overflow * SECP256K1_N_C_2);

    //r->d[2] = secp256k1_u128_to_u64(&t);
	r->d[2] = t.lo;

	//secp256k1_u128_rshift(&t, 64);
	t.lo = t.hi;
	t.hi = 0;
    
	//secp256k1_u128_accum_u64(&t, r->d[3]);
	secp256k1_u128_accum_u64(&t, r->d[3]);

    //r->d[3] = secp256k1_u128_to_u64(&t);
    r->d[3] = t.lo;

	return overflow;
}
static void secp256k1_scalar_set_b32(secp256k1_scalar *r, const unsigned char *b32, int *overflow) {
    int over;
    r->d[0] = (ulong)b32[31] | (ulong)b32[30] << 8 | (ulong)b32[29] << 16 | (ulong)b32[28] << 24 | (ulong)b32[27] << 32 | (ulong)b32[26] << 40 | (ulong)b32[25] << 48 | (ulong)b32[24] << 56;
    r->d[1] = (ulong)b32[23] | (ulong)b32[22] << 8 | (ulong)b32[21] << 16 | (ulong)b32[20] << 24 | (ulong)b32[19] << 32 | (ulong)b32[18] << 40 | (ulong)b32[17] << 48 | (ulong)b32[16] << 56;
    r->d[2] = (ulong)b32[15] | (ulong)b32[14] << 8 | (ulong)b32[13] << 16 | (ulong)b32[12] << 24 | (ulong)b32[11] << 32 | (ulong)b32[10] << 40 | (ulong)b32[9] << 48 | (ulong)b32[8] << 56;
    r->d[3] = (ulong)b32[7] | (ulong)b32[6] << 8 | (ulong)b32[5] << 16 | (ulong)b32[4] << 24 | (ulong)b32[3] << 32 | (ulong)b32[2] << 40 | (ulong)b32[1] << 48 | (ulong)b32[0] << 56;
    over = secp256k1_scalar_reduce(r, secp256k1_scalar_check_overflow(r));
    if (overflow) {
        *overflow = over;
    }
}
static void secp256k1_scalar_get_b32(uchar *bin, const secp256k1_scalar* a) {
    bin[0]  = a->d[3] >> 56; bin[1]  = a->d[3] >> 48; bin[2]  = a->d[3] >> 40; bin[3]  = a->d[3] >> 32; bin[4]  = a->d[3] >> 24; bin[5]  = a->d[3] >> 16; bin[6]  = a->d[3] >> 8; bin[7]  = a->d[3];
    bin[8]  = a->d[2] >> 56; bin[9]  = a->d[2] >> 48; bin[10] = a->d[2] >> 40; bin[11] = a->d[2] >> 32; bin[12] = a->d[2] >> 24; bin[13] = a->d[2] >> 16; bin[14] = a->d[2] >> 8; bin[15] = a->d[2];
    bin[16] = a->d[1] >> 56; bin[17] = a->d[1] >> 48; bin[18] = a->d[1] >> 40; bin[19] = a->d[1] >> 32; bin[20] = a->d[1] >> 24; bin[21] = a->d[1] >> 16; bin[22] = a->d[1] >> 8; bin[23] = a->d[1];
    bin[24] = a->d[0] >> 56; bin[25] = a->d[0] >> 48; bin[26] = a->d[0] >> 40; bin[27] = a->d[0] >> 32; bin[28] = a->d[0] >> 24; bin[29] = a->d[0] >> 16; bin[30] = a->d[0] >> 8; bin[31] = a->d[0];
}
static uint secp256k1_scalar_get_bits(const secp256k1_scalar *a, uint offset, uint count) {
    return (a->d[offset >> 6] >> (offset & 0x3F)) & ((((ulong)1) << count) - 1);
}
static uint secp256k1_scalar_get_bits_var(const secp256k1_scalar *a, uint offset, uint count) {
    if ((offset + count - 1) >> 6 == offset >> 6) {
        return secp256k1_scalar_get_bits(a, offset, count);
    } else {
        return ((a->d[offset >> 6] >> (offset & 0x3F)) | (a->d[(offset >> 6) + 1] << (64 - (offset & 0x3F)))) & ((((ulong)1) << count) - 1);
    }
}
static void secp256k1_scalar_from_signed62(secp256k1_scalar *r, const secp256k1_modinv64_signed62 *a) {
    const ulong a0 = a->v[0], a1 = a->v[1], a2 = a->v[2], a3 = a->v[3], a4 = a->v[4];
    r->d[0] = a0      | a1 << 62;
    r->d[1] = a1 >> 2 | a2 << 60;
    r->d[2] = a2 >> 4 | a3 << 58;
    r->d[3] = a3 >> 6 | a4 << 56;
}
static void secp256k1_scalar_to_signed62(secp256k1_modinv64_signed62 *r, const secp256k1_scalar *a) {
    const ulong M62 = ULONG_MAX >> 2;
    const ulong a0 = a->d[0], a1 = a->d[1], a2 = a->d[2], a3 = a->d[3];
    r->v[0] =  a0                   & M62;
    r->v[1] = (a0 >> 62 | a1 <<  2) & M62;
    r->v[2] = (a1 >> 60 | a2 <<  4) & M62;
    r->v[3] = (a2 >> 58 | a3 <<  6) & M62;
    r->v[4] =  a3 >> 56;
}
static void secp256k1_scalar_cadd_bit(secp256k1_scalar *r, unsigned int bit, int flag) {
    secp256k1_uint128 t;
    int vflag = flag;
    bit += ((uint) vflag - 1) & 0x100;  /* forcing (bit >> 6) > 3 makes this a noop */
    secp256k1_u128_from_u64(&t, r->d[0]);
    secp256k1_u128_accum_u64(&t, ((ulong)((bit >> 6) == 0)) << (bit & 0x3F));
    r->d[0] = secp256k1_u128_to_u64(&t); secp256k1_u128_rshift(&t, 64);
    secp256k1_u128_accum_u64(&t, r->d[1]);
    secp256k1_u128_accum_u64(&t, ((ulong)((bit >> 6) == 1)) << (bit & 0x3F));
    r->d[1] = secp256k1_u128_to_u64(&t); secp256k1_u128_rshift(&t, 64);
    secp256k1_u128_accum_u64(&t, r->d[2]);
    secp256k1_u128_accum_u64(&t, ((ulong)((bit >> 6) == 2)) << (bit & 0x3F));
    r->d[2] = secp256k1_u128_to_u64(&t); secp256k1_u128_rshift(&t, 64);
    secp256k1_u128_accum_u64(&t, r->d[3]);
    secp256k1_u128_accum_u64(&t, ((ulong)((bit >> 6) == 3)) << (bit & 0x3F));
    r->d[3] = secp256k1_u128_to_u64(&t);
}
static void secp256k1_scalar_inverse_var(secp256k1_scalar *r, const secp256k1_scalar *x) {
    secp256k1_modinv64_signed62 s;

    secp256k1_scalar_to_signed62(&s, x);
    secp256k1_modinv64_var(&s, &secp256k1_const_modinfo_scalar);
    secp256k1_scalar_from_signed62(r, &s);
}
static int secp256k1_scalar_add(secp256k1_scalar *r, const secp256k1_scalar *a, const secp256k1_scalar *b) {
    int overflow;
    secp256k1_uint128 t;
    secp256k1_u128_from_u64(&t, a->d[0]);
    secp256k1_u128_accum_u64(&t, b->d[0]);
    r->d[0] = secp256k1_u128_to_u64(&t); secp256k1_u128_rshift(&t, 64);
    secp256k1_u128_accum_u64(&t, a->d[1]);
    secp256k1_u128_accum_u64(&t, b->d[1]);
    r->d[1] = secp256k1_u128_to_u64(&t); secp256k1_u128_rshift(&t, 64);
    secp256k1_u128_accum_u64(&t, a->d[2]);
    secp256k1_u128_accum_u64(&t, b->d[2]);
    r->d[2] = secp256k1_u128_to_u64(&t); secp256k1_u128_rshift(&t, 64);
    secp256k1_u128_accum_u64(&t, a->d[3]);
    secp256k1_u128_accum_u64(&t, b->d[3]);
    r->d[3] = secp256k1_u128_to_u64(&t); secp256k1_u128_rshift(&t, 64);
    overflow = secp256k1_u128_to_u64(&t) + secp256k1_scalar_check_overflow(r);
    secp256k1_scalar_reduce(r, overflow);
    return overflow;
}
static void secp256k1_scalar_negate(secp256k1_scalar *r, const secp256k1_scalar *a) {
    ulong nonzero = 0xFFFFFFFFFFFFFFFFUL * (secp256k1_scalar_is_zero(a) == 0);
    secp256k1_uint128 t;
    secp256k1_u128_from_u64(&t, ~a->d[0]);
    secp256k1_u128_accum_u64(&t, SECP256K1_N_0 + 1);
    r->d[0] = secp256k1_u128_to_u64(&t) & nonzero; secp256k1_u128_rshift(&t, 64);
    secp256k1_u128_accum_u64(&t, ~a->d[1]);
    secp256k1_u128_accum_u64(&t, SECP256K1_N_1);
    r->d[1] = secp256k1_u128_to_u64(&t) & nonzero; secp256k1_u128_rshift(&t, 64);
    secp256k1_u128_accum_u64(&t, ~a->d[2]);
    secp256k1_u128_accum_u64(&t, SECP256K1_N_2);
    r->d[2] = secp256k1_u128_to_u64(&t) & nonzero; secp256k1_u128_rshift(&t, 64);
    secp256k1_u128_accum_u64(&t, ~a->d[3]);
    secp256k1_u128_accum_u64(&t, SECP256K1_N_3);
    r->d[3] = secp256k1_u128_to_u64(&t) & nonzero;
}
static void secp256k1_scalar_reduce_512(secp256k1_scalar *r, const ulong *l) {
    secp256k1_uint128 c128;

    ulong c, c0, c1, c2;
    ulong n0 = l[4], n1 = l[5], n2 = l[6], n3 = l[7];
    ulong m0, m1, m2, m3, m4, m5; uint m6;
    ulong p0, p1, p2, p3; uint p4;

    /* Reduce 512 bits into 385. */
    /* m[0..6] = l[0..3] + n[0..3] * SECP256K1_N_C. */
    c0 = l[0]; c1 = 0; c2 = 0;
    muladd_fast(n0, SECP256K1_N_C_0, &c0, &c1);
    extract_fast(&m0, &c0, &c1);
    sumadd_fast(l[1], &c0, &c1);
	muladd_ulong(n1, SECP256K1_N_C_0, &c0, &c1, &c2);
    muladd_ulong(n0, SECP256K1_N_C_1, &c0, &c1, &c2);
    extract_ulong(&m1, &c0, &c1, &c2);
    sumadd(l[2], &c0, &c1, &c2);
	muladd_ulong(n2, SECP256K1_N_C_0, &c0, &c1, &c2);
    muladd_ulong(n1, SECP256K1_N_C_1, &c0, &c1, &c2);
    sumadd(n0, &c0, &c1, &c2);
    extract_ulong(&m2, &c0, &c1, &c2);
    sumadd(l[3], &c0, &c1, &c2);
	muladd_ulong(n3, SECP256K1_N_C_0, &c0, &c1, &c2);
    muladd_ulong(n2, SECP256K1_N_C_1, &c0, &c1, &c2);
    sumadd(n1, &c0, &c1, &c2);
    extract_ulong(&m3, &c0, &c1, &c2);
    muladd_ulong(n3, SECP256K1_N_C_1, &c0, &c1, &c2);
    sumadd(n2, &c0, &c1, &c2);
    extract_ulong(&m4, &c0, &c1, &c2);
    sumadd_fast(n3, &c0, &c1);
    extract_fast(&m5, &c0, &c1);
    m6 = c0;

    /* Reduce 385 bits into 258. */
    /* p[0..4] = m[0..3] + m[4..6] * SECP256K1_N_C. */
    c0 = m0; c1 = 0; c2 = 0;
    muladd_fast(m4, SECP256K1_N_C_0, &c0, &c1);
    extract_fast(&p0, &c0, &c1);
    sumadd_fast(m1, &c0, &c1);
    muladd_ulong(m5, SECP256K1_N_C_0, &c0, &c1, &c2);
    muladd_ulong(m4, SECP256K1_N_C_1, &c0, &c1, &c2);
    extract_ulong(&p1, &c0, &c1, &c2);
    sumadd(m2, &c0, &c1, &c2);
    muladd_ulong(m6, SECP256K1_N_C_0, &c0, &c1, &c2);
    muladd_ulong(m5, SECP256K1_N_C_1, &c0, &c1, &c2);
	sumadd(m4, &c0, &c1, &c2);
    extract_ulong(&p2, &c0, &c1, &c2);
    sumadd_fast(m3, &c0, &c1);
    muladd_fast(m6, SECP256K1_N_C_1, &c0, &c1);
    sumadd_fast(m5, &c0, &c1);
    extract_fast(&p3, &c0, &c1);
    p4 = c0 + m6;

    /* Reduce 258 bits into 256. */
    /* r[0..3] = p[0..3] + p[4] * SECP256K1_N_C. */
    secp256k1_u128_from_u64(&c128, p0);
    secp256k1_u128_accum_mul(&c128, SECP256K1_N_C_0, p4);
    r->d[0] = secp256k1_u128_to_u64(&c128); secp256k1_u128_rshift(&c128, 64);
    secp256k1_u128_accum_u64(&c128, p1);
    secp256k1_u128_accum_mul(&c128, SECP256K1_N_C_1, p4);
    r->d[1] = secp256k1_u128_to_u64(&c128); secp256k1_u128_rshift(&c128, 64);
    secp256k1_u128_accum_u64(&c128, p2);
    secp256k1_u128_accum_u64(&c128, p4);
    r->d[2] = secp256k1_u128_to_u64(&c128); secp256k1_u128_rshift(&c128, 64);
    secp256k1_u128_accum_u64(&c128, p3);
    r->d[3] = secp256k1_u128_to_u64(&c128);
    c = secp256k1_u128_hi_u64(&c128);

    /* Final reduction of r. */
    secp256k1_scalar_reduce(r, c + secp256k1_scalar_check_overflow(r));
}
static void secp256k1_scalar_mul_512_const(ulong l[8], const secp256k1_scalar *a, __constant const secp256k1_scalar *b) {
    /* 160 bit accumulator. */
    ulong c0 = 0, c1 = 0;
    uint c2 = 0;

    /* l[0..7] = a[0..3] * b[0..3]. */
    muladd_fast(a->d[0], b->d[0], &c0, &c1);
    extract_fast(&l[0], &c0, &c1);
    muladd(a->d[0], b->d[1], &c0, &c1, &c2);
    muladd(a->d[1], b->d[0], &c0, &c1, &c2);
    extract(&l[1], &c0, &c1, &c2);
    muladd(a->d[0], b->d[2], &c0, &c1, &c2);
    muladd(a->d[1], b->d[1], &c0, &c1, &c2);
    muladd(a->d[2], b->d[0], &c0, &c1, &c2);
    extract(&l[2], &c0, &c1, &c2);
    muladd(a->d[0], b->d[3], &c0, &c1, &c2);
    muladd(a->d[1], b->d[2], &c0, &c1, &c2);
    muladd(a->d[2], b->d[1], &c0, &c1, &c2);
    muladd(a->d[3], b->d[0], &c0, &c1, &c2);
    extract(&l[3], &c0, &c1, &c2);
    muladd(a->d[1], b->d[3], &c0, &c1, &c2);
    muladd(a->d[2], b->d[2], &c0, &c1, &c2);
    muladd(a->d[3], b->d[1], &c0, &c1, &c2);
    extract(&l[4], &c0, &c1, &c2);
    muladd(a->d[2], b->d[3], &c0, &c1, &c2);
    muladd(a->d[3], b->d[2], &c0, &c1, &c2);
    extract(&l[5], &c0, &c1, &c2);
    muladd_fast(a->d[3], b->d[3], &c0, &c1);
    extract_fast(&l[6], &c0, &c1);
    l[7] = c0;
}
static void secp256k1_scalar_mul_const(secp256k1_scalar *r, const secp256k1_scalar *a, __constant const secp256k1_scalar *b) {
    ulong l[8];
    secp256k1_scalar_mul_512_const(l, a, b);
    secp256k1_scalar_reduce_512(r, l);
}
static void secp256k1_scalar_mul_512(ulong l[8], const secp256k1_scalar *a, const secp256k1_scalar *b) {
    /* 160 bit accumulator. */
    ulong c0 = 0, c1 = 0;
    uint c2 = 0;

    /* l[0..7] = a[0..3] * b[0..3]. */
    muladd_fast(a->d[0], b->d[0], &c0, &c1);
    extract_fast(&l[0], &c0, &c1);
    muladd(a->d[0], b->d[1], &c0, &c1, &c2);
    muladd(a->d[1], b->d[0], &c0, &c1, &c2);
    extract(&l[1], &c0, &c1, &c2);
    muladd(a->d[0], b->d[2], &c0, &c1, &c2);
    muladd(a->d[1], b->d[1], &c0, &c1, &c2);
    muladd(a->d[2], b->d[0], &c0, &c1, &c2);
    extract(&l[2], &c0, &c1, &c2);
    muladd(a->d[0], b->d[3], &c0, &c1, &c2);
    muladd(a->d[1], b->d[2], &c0, &c1, &c2);
    muladd(a->d[2], b->d[1], &c0, &c1, &c2);
    muladd(a->d[3], b->d[0], &c0, &c1, &c2);
    extract(&l[3], &c0, &c1, &c2);
    muladd(a->d[1], b->d[3], &c0, &c1, &c2);
    muladd(a->d[2], b->d[2], &c0, &c1, &c2);
    muladd(a->d[3], b->d[1], &c0, &c1, &c2);
    extract(&l[4], &c0, &c1, &c2);
    muladd(a->d[2], b->d[3], &c0, &c1, &c2);
    muladd(a->d[3], b->d[2], &c0, &c1, &c2);
    extract(&l[5], &c0, &c1, &c2);
    muladd_fast(a->d[3], b->d[3], &c0, &c1);
    extract_fast(&l[6], &c0, &c1);
    l[7] = c0;
}
static void secp256k1_scalar_mul(secp256k1_scalar *r, const secp256k1_scalar *a, const secp256k1_scalar *b) {
    ulong l[8];
    secp256k1_scalar_mul_512(l, a, b);
    secp256k1_scalar_reduce_512(r, l);
}
static void secp256k1_scalar_mul_shift_var(secp256k1_scalar *r, const secp256k1_scalar *a, __constant const secp256k1_scalar *b, uint shift) {
    ulong l[8];
    unsigned int shiftlimbs;
    unsigned int shiftlow;
    unsigned int shifthigh;
    secp256k1_scalar_mul_512_const(l, a, b);
    shiftlimbs = shift >> 6;
    shiftlow = shift & 0x3F;
    shifthigh = 64 - shiftlow;
    r->d[0] = shift < 512 ? (l[0 + shiftlimbs] >> shiftlow | (shift < 448 && shiftlow ? (l[1 + shiftlimbs] << shifthigh) : 0)) : 0;
    r->d[1] = shift < 448 ? (l[1 + shiftlimbs] >> shiftlow | (shift < 384 && shiftlow ? (l[2 + shiftlimbs] << shifthigh) : 0)) : 0;
    r->d[2] = shift < 384 ? (l[2 + shiftlimbs] >> shiftlow | (shift < 320 && shiftlow ? (l[3 + shiftlimbs] << shifthigh) : 0)) : 0;
    r->d[3] = shift < 320 ? (l[3 + shiftlimbs] >> shiftlow) : 0;
    secp256k1_scalar_cadd_bit(r, 0, (l[(shift - 1) >> 6] >> ((shift - 1) & 0x3f)) & 1);
}
static void secp256k1_scalar_split_128(secp256k1_scalar *r1, secp256k1_scalar *r2, const secp256k1_scalar *k) {
    r1->d[0] = k->d[0];
    r1->d[1] = k->d[1];
    r1->d[2] = 0;
    r1->d[3] = 0;
    r2->d[0] = k->d[2];
    r2->d[1] = k->d[3];
    r2->d[2] = 0;
    r2->d[3] = 0;
}
static void secp256k1_scalar_split_lambda(secp256k1_scalar *r1, secp256k1_scalar *r2, const secp256k1_scalar *k) {
    secp256k1_scalar c1, c2;

    /* these _var calls are constant time since the shift amount is constant */
    secp256k1_scalar_mul_shift_var(&c1, k, &const_g1, 384);
    secp256k1_scalar_mul_shift_var(&c2, k, &const_g2, 384);
    secp256k1_scalar_mul_const(&c1, &c1, &const_minus_b1);
    secp256k1_scalar_mul_const(&c2, &c2, &const_minus_b2);
    secp256k1_scalar_add(r2, &c1, &c2);
    secp256k1_scalar_mul_const(r1, r2, &const_lambda);
    secp256k1_scalar_negate(r1, r1);
    secp256k1_scalar_add(r1, r1, k);
}

typedef struct { unsigned char data[64]; } secp256k1_pubkey;
typedef struct { unsigned char data[64]; } secp256k1_ecdsa_signature;
static void secp256k1_ecdsa_signature_load(secp256k1_scalar* r, secp256k1_scalar* s, const secp256k1_ecdsa_signature* sig) {
    if (sizeof(secp256k1_scalar) == 32) {
        /* When the secp256k1_scalar type is exactly 32 byte, use its
         * representation inside secp256k1_ecdsa_signature, as conversion is very fast.
         * Note that secp256k1_ecdsa_signature_save must use the same representation. */
        memcpy(r, &sig->data[0], 32);
        memcpy(s, &sig->data[32], 32);
    } else {
        secp256k1_scalar_set_b32(r, &sig->data[0], 0);
        secp256k1_scalar_set_b32(s, &sig->data[32], 0);
    }
}
static int secp256k1_pubkey_load(secp256k1_ge* ge, const secp256k1_pubkey* pubkey) {
    if (sizeof(secp256k1_ge_storage) == 64) {
        /* When the secp256k1_ge_storage type is exactly 64 byte, use its
         * representation inside secp256k1_pubkey, as conversion is very fast.
         * Note that secp256k1_pubkey_save must use the same representation. */
        secp256k1_ge_storage s;

		// TODO: Implement custom memcpy
        memcpy(&s, &pubkey->data[0], sizeof(s));
        secp256k1_ge_from_storage(ge, &s);
    } else {
        /* Otherwise, fall back to 32-byte big endian for X and Y. */
        secp256k1_fe x, y;
        secp256k1_fe_set_b32_mod(&x, pubkey->data);
        secp256k1_fe_set_b32_mod(&y, pubkey->data + 32);
        secp256k1_ge_set_xy(ge, &x, &y);
    }
    return 1;
}

struct secp256k1_strauss_point_state {
    int wnaf_na_1[129];
    int wnaf_na_lam[129];
    int bits_na_1;
    int bits_na_lam;
};
struct secp256k1_strauss_state {
    /* aux is used to hold z-ratios, and then used to hold pre_a[i].x * BETA values. */
    secp256k1_fe* aux;
    secp256k1_ge* pre_a;
    struct secp256k1_strauss_point_state* ps;
};

static int secp256k1_ecmult_wnaf(int *wnaf, int len, const secp256k1_scalar *a, int w) {
    secp256k1_scalar s;
    int last_set_bit = -1;
    int bit = 0;
    int sign = 1;
    int carry = 0;

    //memset(wnaf, 0, len * sizeof(wnaf[0]));
	for (int i = 0; i < len; i += 1) {
		wnaf[i] = 0;
	}

    s = *a;
    if (secp256k1_scalar_get_bits(&s, 255, 1)) {
        secp256k1_scalar_negate(&s, &s);
        sign = -1;
    }

    while (bit < len) {
        int now;
        int word;
        if (secp256k1_scalar_get_bits(&s, bit, 1) == (uint)carry) {
            bit++;
            continue;
        }

        now = w;
        if (now > len - bit) {
            now = len - bit;
        }

        word = secp256k1_scalar_get_bits_var(&s, bit, now) + carry;

        carry = (word >> (w-1)) & 1;
        word -= carry << w;

        wnaf[bit] = sign * word;
        last_set_bit = bit;

        bit += now;
    }

    return last_set_bit + 1;
}
static void secp256k1_ecmult_odd_multiples_table(int n, secp256k1_ge *pre_a, secp256k1_fe *zr, secp256k1_fe *z, const secp256k1_gej *a) {
    secp256k1_gej d, ai;
    secp256k1_ge d_ge;
    int i;

    secp256k1_gej_double_var(&d, a, 0);

    /*
     * Perform the additions using an isomorphic curve Y^2 = X^3 + 7*C^6 where C := d.z.
     * The isomorphism, phi, maps a secp256k1 point (x, y) to the point (x*C^2, y*C^3) on the other curve.
     * In Jacobian coordinates phi maps (x, y, z) to (x*C^2, y*C^3, z) or, equivalently to (x, y, z/C).
     *
     *     phi(x, y, z) = (x*C^2, y*C^3, z) = (x, y, z/C)
     *   d_ge := phi(d) = (d.x, d.y, 1)
     *     ai := phi(a) = (a.x*C^2, a.y*C^3, a.z)
     *
     * The group addition functions work correctly on these isomorphic curves.
     * In particular phi(d) is easy to represent in affine coordinates under this isomorphism.
     * This lets us use the faster secp256k1_gej_add_ge_var group addition function that we wouldn't be able to use otherwise.
     */
    secp256k1_ge_set_xy(&d_ge, &d.x, &d.y);
    secp256k1_ge_set_gej_zinv(&pre_a[0], a, &d.z);
    secp256k1_gej_set_ge(&ai, &pre_a[0]);
    ai.z = a->z;

    /* pre_a[0] is the point (a.x*C^2, a.y*C^3, a.z*C) which is equivalent to a.
     * Set zr[0] to C, which is the ratio between the omitted z(pre_a[0]) value and a.z.
     */
    zr[0] = d.z;

    for (i = 1; i < n; i++) {
        secp256k1_gej_add_ge_var(&ai, &ai, &d_ge, &zr[i]);
        secp256k1_ge_set_xy(&pre_a[i], &ai.x, &ai.y);
    }

    /* Multiply the last z-coordinate by C to undo the isomorphism.
     * Since the z-coordinates of the pre_a values are implied by the zr array of z-coordinate ratios,
     * undoing the isomorphism here undoes the isomorphism for all pre_a values.
     */
    secp256k1_fe_mul(z, &ai.z, &d.z);
}
static void secp256k1_ecmult_table_get_ge(secp256k1_ge *r, const secp256k1_ge *pre, int n, int w) {
    if (n > 0) {
        *r = pre[(n-1)/2];
    } else {
        *r = pre[(-n-1)/2];
        secp256k1_fe_negate(&(r->y), &(r->y), 1);
    }
}
static void secp256k1_ecmult_table_get_ge_lambda(secp256k1_ge *r, const secp256k1_ge *pre, const secp256k1_fe *x, int n, int w) {
    if (n > 0) {
        secp256k1_ge_set_xy(r, &x[(n-1)/2], &pre[(n-1)/2].y);
    } else {
        secp256k1_ge_set_xy(r, &x[(-n-1)/2], &pre[(-n-1)/2].y);
        secp256k1_fe_negate(&(r->y), &(r->y), 1);
    }
}
static void secp256k1_ecmult_table_get_ge_storage(secp256k1_ge *r, const secp256k1_ge_storage *pre, int n, int w) {
    if (n > 0) {
        secp256k1_ge_from_storage(r, &pre[(n-1)/2]);
    } else {
        secp256k1_ge_from_storage(r, &pre[(-n-1)/2]);
        secp256k1_fe_negate(&(r->y), &(r->y), 1);
    }
}
static void secp256k1_ecmult_table_get_ge_storage_const(secp256k1_ge *r, __constant const secp256k1_ge_storage *pre, int n, int w) {
    if (n > 0) {
        secp256k1_ge_from_storage_const(r, &pre[(n-1)/2]);
    } else {
        secp256k1_ge_from_storage_const(r, &pre[(-n-1)/2]);
        secp256k1_fe_negate(&(r->y), &(r->y), 1);
    }
}
static void secp256k1_ecmult_strauss_wnaf(const struct secp256k1_strauss_state *state, secp256k1_gej *r, ulong num, const secp256k1_gej *a, const secp256k1_scalar *na, const secp256k1_scalar *ng) {
    secp256k1_ge tmpa;
    secp256k1_fe Z;
    /* Split G factors. */
    secp256k1_scalar ng_1, ng_128;
    int wnaf_ng_1[129];
    int bits_ng_1 = 0;
    int wnaf_ng_128[129];
    int bits_ng_128 = 0;
    int i;
    int bits = 0;
    ulong np;
    ulong no = 0;

    secp256k1_fe_set_int(&Z, 1);
    for (np = 0; np < num; ++np) {
        secp256k1_gej tmp;
        secp256k1_scalar na_1, na_lam;
        if (secp256k1_scalar_is_zero(&na[np]) || secp256k1_gej_is_infinity(&a[np])) {
            continue;
        }
        /* split na into na_1 and na_lam (where na = na_1 + na_lam*lambda, and na_1 and na_lam are ~128 bit) */
        secp256k1_scalar_split_lambda(&na_1, &na_lam, &na[np]);

        /* build wnaf representation for na_1 and na_lam. */
        state->ps[no].bits_na_1   = secp256k1_ecmult_wnaf(state->ps[no].wnaf_na_1,   129, &na_1,   WINDOW_A);
        state->ps[no].bits_na_lam = secp256k1_ecmult_wnaf(state->ps[no].wnaf_na_lam, 129, &na_lam, WINDOW_A);

        if (state->ps[no].bits_na_1 > bits) {
            bits = state->ps[no].bits_na_1;
        }
        if (state->ps[no].bits_na_lam > bits) {
            bits = state->ps[no].bits_na_lam;
        }

        /* Calculate odd multiples of a.
         * All multiples are brought to the same Z 'denominator', which is stored
         * in Z. Due to secp256k1' isomorphism we can do all operations pretending
         * that the Z coordinate was 1, use affine addition formulae, and correct
         * the Z coordinate of the result once at the end.
         * The exception is the precomputed G table points, which are actually
         * affine. Compared to the base used for other points, they have a Z ratio
         * of 1/Z, so we can use secp256k1_gej_add_zinv_var, which uses the same
         * isomorphism to efficiently add with a known Z inverse.
         */
        tmp = a[np];
        if (no) {
            secp256k1_gej_rescale(&tmp, &Z);
        }
        secp256k1_ecmult_odd_multiples_table(ECMULT_TABLE_SIZE(WINDOW_A), state->pre_a + no * ECMULT_TABLE_SIZE(WINDOW_A), state->aux + no * ECMULT_TABLE_SIZE(WINDOW_A), &Z, &tmp);
        if (no) secp256k1_fe_mul(state->aux + no * ECMULT_TABLE_SIZE(WINDOW_A), state->aux + no * ECMULT_TABLE_SIZE(WINDOW_A), &(a[np].z));

        ++no;
    }

    /* Bring them to the same Z denominator. */
    secp256k1_ge_table_set_globalz(ECMULT_TABLE_SIZE(WINDOW_A) * no, state->pre_a, state->aux);

    for (np = 0; np < no; ++np) {
        for (i = 0; i < ECMULT_TABLE_SIZE(WINDOW_A); i++) {
            secp256k1_fe_mul_const(&state->aux[np * ECMULT_TABLE_SIZE(WINDOW_A) + i], &state->pre_a[np * ECMULT_TABLE_SIZE(WINDOW_A) + i].x, &const_beta);
        }
    }

    if (ng) {
        /* split ng into ng_1 and ng_128 (where gn = gn_1 + gn_128*2^128, and gn_1 and gn_128 are ~128 bit) */
        secp256k1_scalar_split_128(&ng_1, &ng_128, ng);

        /* Build wnaf representation for ng_1 and ng_128 */
        bits_ng_1   = secp256k1_ecmult_wnaf(wnaf_ng_1,   129, &ng_1,   WINDOW_G);
        bits_ng_128 = secp256k1_ecmult_wnaf(wnaf_ng_128, 129, &ng_128, WINDOW_G);
        if (bits_ng_1 > bits) {
            bits = bits_ng_1;
        }
        if (bits_ng_128 > bits) {
            bits = bits_ng_128;
        }
    }

    secp256k1_gej_set_infinity(r);

    for (i = bits - 1; i >= 0; i--) {
        int n;
        secp256k1_gej_double_var(r, r, 0);
        for (np = 0; np < no; ++np) {
            if (i < state->ps[np].bits_na_1 && (n = state->ps[np].wnaf_na_1[i])) {
                secp256k1_ecmult_table_get_ge(&tmpa, state->pre_a + np * ECMULT_TABLE_SIZE(WINDOW_A), n, WINDOW_A);
                secp256k1_gej_add_ge_var(r, r, &tmpa, 0);
            }
            if (i < state->ps[np].bits_na_lam && (n = state->ps[np].wnaf_na_lam[i])) {
                secp256k1_ecmult_table_get_ge_lambda(&tmpa, state->pre_a + np * ECMULT_TABLE_SIZE(WINDOW_A), state->aux + np * ECMULT_TABLE_SIZE(WINDOW_A), n, WINDOW_A);
                secp256k1_gej_add_ge_var(r, r, &tmpa, 0);
            }
        }
        if (i < bits_ng_1 && (n = wnaf_ng_1[i])) {
            secp256k1_ecmult_table_get_ge_storage_const(&tmpa, secp256k1_pre_g, n, WINDOW_G);
            secp256k1_gej_add_zinv_var(r, r, &tmpa, &Z);
        }
        if (i < bits_ng_128 && (n = wnaf_ng_128[i])) {
            secp256k1_ecmult_table_get_ge_storage_const(&tmpa, secp256k1_pre_g_128, n, WINDOW_G);
            secp256k1_gej_add_zinv_var(r, r, &tmpa, &Z);
        }
    }

    if (!r->infinity) {
        secp256k1_fe_mul(&r->z, &r->z, &Z);
    }
}
static void secp256k1_ecmult(secp256k1_gej *r, const secp256k1_gej *a, const secp256k1_scalar *na, const secp256k1_scalar *ng) {
    secp256k1_fe aux[ECMULT_TABLE_SIZE(WINDOW_A)];
    secp256k1_ge pre_a[ECMULT_TABLE_SIZE(WINDOW_A)];
    struct secp256k1_strauss_point_state ps[1];
    struct secp256k1_strauss_state state;

    state.aux = aux;
    state.pre_a = pre_a;
    state.ps = ps;
    secp256k1_ecmult_strauss_wnaf(&state, r, 1, a, na, ng);
}
static int secp256k1_ecdsa_sig_verify(const secp256k1_scalar *sigr, const secp256k1_scalar *sigs, const secp256k1_ge *pubkey, const secp256k1_scalar *message) {
    uchar c[32];
    secp256k1_scalar sn, u1, u2;
    secp256k1_fe xr;
    secp256k1_gej pubkeyj;
    secp256k1_gej pr;

    if (secp256k1_scalar_is_zero(sigr) || secp256k1_scalar_is_zero(sigs)) {
        return 0;
    }

    secp256k1_scalar_inverse_var(&sn, sigs);
    secp256k1_scalar_mul(&u1, &sn, message);
    secp256k1_scalar_mul(&u2, &sn, sigr);
    secp256k1_gej_set_ge(&pubkeyj, pubkey);
    secp256k1_ecmult(&pr, &pubkeyj, &u2, &u1);
    if (secp256k1_gej_is_infinity(&pr)) {
        return 0;
    }

    secp256k1_scalar_get_b32(c, sigr);
    /* we can ignore the fe_set_b32_limit return value, because we know the input is in range */
    (void)secp256k1_fe_set_b32_limit(&xr, c);

    /** We now have the recomputed R point in pr, and its claimed x coordinate (modulo n)
     *  in xr. Naively, we would extract the x coordinate from pr (requiring a inversion modulo p),
     *  compute the remainder modulo n, and compare it to xr. However:
     *
     *        xr == X(pr) mod n
     *    <=> exists h. (xr + h * n < p && xr + h * n == X(pr))
     *    [Since 2 * n > p, h can only be 0 or 1]
     *    <=> (xr == X(pr)) || (xr + n < p && xr + n == X(pr))
     *    [In Jacobian coordinates, X(pr) is pr.x / pr.z^2 mod p]
     *    <=> (xr == pr.x / pr.z^2 mod p) || (xr + n < p && xr + n == pr.x / pr.z^2 mod p)
     *    [Multiplying both sides of the equations by pr.z^2 mod p]
     *    <=> (xr * pr.z^2 mod p == pr.x) || (xr + n < p && (xr + n) * pr.z^2 mod p == pr.x)
     *
     *  Thus, we can avoid the inversion, but we have to check both cases separately.
     *  secp256k1_gej_eq_x implements the (xr * pr.z^2 mod p == pr.x) test.
     */
    if (secp256k1_gej_eq_x_var(&xr, &pr)) {
        /* xr * pr.z^2 mod p == pr.x, so the signature is valid. */
        return 1;
    }
    if (secp256k1_fe_cmp_var_const(&xr, &secp256k1_ecdsa_const_p_minus_order) >= 0) {
        /* xr + n >= p, so we can skip testing the second case. */
        return 0;
    }
    secp256k1_fe_add_const(&xr, &secp256k1_ecdsa_const_order_as_fe);
    if (secp256k1_gej_eq_x_var(&xr, &pr)) {
        /* (xr + n) * pr.z^2 mod p == pr.x, so the signature is valid. */
        return 1;
    }
    return 0;
}

static int secp256k1_ecdsa_verify(const secp256k1_ecdsa_signature *sig, const unsigned char *msghash32, const secp256k1_pubkey *pubkey) {
    secp256k1_ge q;
    secp256k1_scalar r, s;
    secp256k1_scalar m;

    secp256k1_scalar_set_b32(&m, msghash32, 0);
    secp256k1_ecdsa_signature_load(&r, &s, sig);
    return (!secp256k1_scalar_is_high(&s) &&
            secp256k1_pubkey_load(&q, pubkey) &&
            secp256k1_ecdsa_sig_verify(&r, &s, &q, &m));
}
