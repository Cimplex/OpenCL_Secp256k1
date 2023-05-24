// Constants
/* Limbs of half the secp256k1 order. */
#define SECP256K1_N_H_0 (0xDFE92F46681B20A0UL)
#define SECP256K1_N_H_1 (0x5D576E7357A4501DUL)
#define SECP256K1_N_H_2 (0xFFFFFFFFFFFFFFFFUL)
#define SECP256K1_N_H_3 (0x7FFFFFFFFFFFFFFFUL)

/* Limbs of the secp256k1 order. */
#define SECP256K1_N_0 (0xBFD25E8CD0364141UL)
#define SECP256K1_N_1 (0xBAAEDCE6AF48A03BUL)
#define SECP256K1_N_2 (0xFFFFFFFFFFFFFFFEUL)
#define SECP256K1_N_3 (0xFFFFFFFFFFFFFFFFUL)

/* Limbs of 2^256 minus the secp256k1 order. */
#define SECP256K1_N_C_0 (~SECP256K1_N_0 + 1)
#define SECP256K1_N_C_1 (~SECP256K1_N_1)
#define SECP256K1_N_C_2 (1)

// OpenCL-Type -> C-Type
typedef struct {
    ulong hi; // Higher 64 bits
    ulong lo; // Lower 64 bits
} secp256k1_uint128;

typedef struct {
    long hi; // Higher 64 bits
    ulong lo; // Lower 64 bits
} secp256k1_int128;

static void secp256k1_i128_add(secp256k1_int128 *r, const secp256k1_int128 *a, const secp256k1_int128 *b) {
    secp256k1_int128 sum;
    secp256k1_int128 carry;

    sum.lo = a->lo + b->lo;
    carry.lo = (sum.lo < a->lo) || (sum.lo < b->lo);

    sum.hi = a->hi + b->hi + carry.lo;
    carry.hi = (sum.hi < a->hi) || (sum.hi < b->hi);

    sum.hi += carry.hi;

    *r = sum;
}

static void secp256k1_i128_mul(secp256k1_int128 *r, long a, long b) {
    ulong lo_a = (ulong)a;
    ulong hi_a = (a < 0) ? ULONG_MAX : 0UL;
    ulong lo_b = (ulong)b;
    ulong hi_b = (b < 0) ? ULONG_MAX : 0UL;

    ulong lo_result = lo_a * lo_b;
    ulong mid_result = lo_a * hi_b + hi_a * lo_b;
    ulong hi_result = hi_a * hi_b;

    mid_result += (lo_result >> 32);
    hi_result += (mid_result >> 32);

    r->lo = (lo_result & 0xFFFFFFFFUL) | ((mid_result & 0xFFFFFFFFUL) << 32);
    r->hi = hi_result;
}

static void secp256k1_i128_accum_mul(secp256k1_int128 *r, long a, long b) {
    secp256k1_int128 ab;
    secp256k1_i128_mul(&ab, a, b);

    secp256k1_int128 temp = *r;
    secp256k1_i128_add(&temp, &temp, &ab);
    *r = temp;
}

typedef struct {
    long v[5];
} secp256k1_modinv64_signed62;

typedef struct {
    /* The modulus in signed62 notation, must be odd and in [3, 2^256]. */
    secp256k1_modinv64_signed62 modulus;

    /* modulus^{-1} mod 2^62 */
    ulong modulus_inv62;
} secp256k1_modinv64_modinfo;

typedef struct {
    long u, v, q, r;
} secp256k1_modinv64_trans2x2;

typedef struct {
    ulong d[4];
} secp256k1_scalar;

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

typedef struct {
    ulong n[4];
} secp256k1_fe_storage;

typedef struct {
    secp256k1_fe x;
    secp256k1_fe y;
    int infinity; /* whether this represents the point at infinity */
} secp256k1_ge;

typedef struct {
    secp256k1_fe_storage x;
    secp256k1_fe_storage y;
} secp256k1_ge_storage;

typedef struct {
    secp256k1_fe x; /* actual X: x/z^2 */
    secp256k1_fe y; /* actual Y: y/z^3 */
    secp256k1_fe z;
    int infinity; /* whether this represents the point at infinity */
} secp256k1_gej;

typedef struct {
    /* Whether the context has been built. */
    int built;

    /* Blinding values used when computing (n-b)G + bG. */
    secp256k1_scalar blind; /* -b */
    secp256k1_gej initial;  /* bG */
} secp256k1_ecmult_gen_context;

struct secp256k1_context_struct {
    secp256k1_ecmult_gen_context ecmult_gen_ctx;
    
	// TODO: Add some way of error checking? not sure what these do yet
	//secp256k1_callback illegal_callback;
    //secp256k1_callback error_callback;
    int declassify;
};

typedef struct secp256k1_context_struct secp256k1_context;

typedef struct {
    uchar data[64];
} secp256k1_ecdsa_signature;

typedef struct {
    uchar data[64];
} secp256k1_pubkey;

static void memcpy_opencl(uchar* src, uchar* dest, size_t numElements)
{
    for (size_t i = 0; i < numElements; ++i)
    {
        dest[i] = src[i];
    }
}

static void secp256k1_u128_from_u64(secp256k1_uint128 *r, ulong a) {
   r->lo = a;
}

static void secp256k1_u128_accum_u64(secp256k1_uint128 *r, ulong a) {
	ulong sum_lo = r->lo + a;
    r->hi += (sum_lo < r->lo) ? 1 : 0;  // Check for overflow
    r->lo = sum_lo;
}

static ulong secp256k1_u128_to_u64(const secp256k1_uint128 *a) {
   return a->lo;
}

static void secp256k1_u128_rshift_64(secp256k1_uint128 *r) {
   r->lo = r->hi;
   r->hi = 0;
}

static void secp256k1_fe_from_storage(secp256k1_fe *r, const secp256k1_fe_storage *a) {
    r->n[0] = a->n[0] & 0xFFFFFFFFFFFFFUL;
    r->n[1] = a->n[0] >> 52 | ((a->n[1] << 12) & 0xFFFFFFFFFFFFFUL);
    r->n[2] = a->n[1] >> 40 | ((a->n[2] << 24) & 0xFFFFFFFFFFFFFUL);
    r->n[3] = a->n[2] >> 28 | ((a->n[3] << 36) & 0xFFFFFFFFFFFFFUL);
    r->n[4] = a->n[3] >> 16;
}

static void secp256k1_fe_set_b32_mod(secp256k1_fe *r, const uchar *a) {
    r->n[0] =  (ulong) a[31]
            | ((ulong) a[30]  << 8  )
            | ((ulong) a[29]  << 16 )
            | ((ulong) a[28]  << 24 )
            | ((ulong) a[27]  << 32 )
            | ((ulong) a[26]  << 40 )
            | ((ulong)(a[25]  & 0xF ) << 48);
    r->n[1] = (ulong)((a[25]  >> 4  ) &  0xF)
            | ((ulong) a[24]  << 4  )
            | ((ulong) a[23]  << 12 )
            | ((ulong) a[22]  << 20 )
            | ((ulong) a[21]  << 28 )
            | ((ulong) a[20]  << 36 )
            | ((ulong) a[19]  << 44 );
    r->n[2] =  (ulong) a[18]
            | ((ulong) a[17]  << 8  )
            | ((ulong) a[16]  << 16 )
            | ((ulong) a[15]  << 24 )
            | ((ulong) a[14]  << 32 )
            | ((ulong) a[13]  << 40 )
            | ((ulong)(a[12]  &  0xF) << 48);
    r->n[3] = (ulong)((a[12]  >> 4  ) &  0xF)
            | ((ulong) a[11]  << 4  )
            | ((ulong) a[10]  << 12 )
            | ((ulong) a[9]   << 20 )
            | ((ulong) a[8]   << 28 )
            | ((ulong) a[7]   << 36 )
            | ((ulong) a[6]   << 44 );
    r->n[4] =  (ulong) a[5]
            | ((ulong) a[4]   << 8  )
            | ((ulong) a[3]   << 16 )
            | ((ulong) a[2]   << 24 )
            | ((ulong) a[1]   << 32 )
            | ((ulong) a[0]   << 40 );
}

static void secp256k1_ge_from_storage(secp256k1_ge *r, const secp256k1_ge_storage *a) {
    secp256k1_fe_from_storage(&r->x, &a->x);
    secp256k1_fe_from_storage(&r->y, &a->y);
    r->infinity = 0;

	// TODO: No verify
    //secp256k1_ge_verify(r);
}

static void secp256k1_ge_set_xy(secp256k1_ge *r, const secp256k1_fe *x, const secp256k1_fe *y) {
    
	// TODO: No Verify
	//secp256k1_fe_verify(x);
    //secp256k1_fe_verify(y);
    
	r->infinity = 0;
    r->x = *x;
    r->y = *y;
    
	// TODO: No Verify
	//secp256k1_ge_verify(r);
}

static int secp256k1_scalar_reduce(secp256k1_scalar *r, uint overflow) {
    secp256k1_uint128 t;

    secp256k1_u128_from_u64(&t, r->d[0]);
    secp256k1_u128_accum_u64(&t, overflow * SECP256K1_N_C_0);

    r->d[0] = secp256k1_u128_to_u64(&t); secp256k1_u128_rshift_64(&t);

	secp256k1_u128_accum_u64(&t, r->d[1]);
    secp256k1_u128_accum_u64(&t, overflow * SECP256K1_N_C_1);

	r->d[1] = secp256k1_u128_to_u64(&t); secp256k1_u128_rshift_64(&t);

	secp256k1_u128_accum_u64(&t, r->d[2]);
    secp256k1_u128_accum_u64(&t, overflow * SECP256K1_N_C_2);

	r->d[2] = secp256k1_u128_to_u64(&t); secp256k1_u128_rshift_64(&t);

	secp256k1_u128_accum_u64(&t, r->d[3]);

	r->d[3] = secp256k1_u128_to_u64(&t);

	return overflow;
}

static int secp256k1_scalar_check_overflow(const secp256k1_scalar *a) {
    int yes = 0;
    int no = 0;
    no  |= (a->d[3] <  SECP256K1_N_3); /* No need for a > check. */
    no  |= (a->d[2] <  SECP256K1_N_2);
    yes |= (a->d[2] >  SECP256K1_N_2) & ~no;
    no  |= (a->d[1] <  SECP256K1_N_1);
    yes |= (a->d[1] >  SECP256K1_N_1) & ~no;
    yes |= (a->d[0] >= SECP256K1_N_0) & ~no;
    return yes;
}

static int secp256k1_scalar_is_high(const secp256k1_scalar *a) {
    int yes = 0;
    int no = 0;
    no  |= (a->d[3] < SECP256K1_N_H_3);
    yes |= (a->d[3] > SECP256K1_N_H_3) & ~no;
    no  |= (a->d[2] < SECP256K1_N_H_2) & ~yes; /* No need for a > check. */
    no  |= (a->d[1] < SECP256K1_N_H_1) & ~yes;
    yes |= (a->d[1] > SECP256K1_N_H_1) & ~no;
    yes |= (a->d[0] > SECP256K1_N_H_0) & ~no;
    return yes;
}

static int secp256k1_scalar_is_zero(const secp256k1_scalar *a) {
    return (a->d[0] | a->d[1] | a->d[2] | a->d[3]) == 0;
}

static void secp256k1_scalar_set_b32(secp256k1_scalar *r, const uchar *b32, int *overflow) {
    int over;
    r->d[0] = (ulong)b32[31] | (ulong)b32[30] << 8 | (ulong)b32[29] << 16 | (ulong)b32[28] << 24 | (ulong)b32[27] << 32 | (ulong)b32[26] << 40 | (ulong)b32[25] << 48 | (ulong)b32[24] << 56;
    r->d[1] = (ulong)b32[23] | (ulong)b32[22] << 8 | (ulong)b32[21] << 16 | (ulong)b32[20] << 24 | (ulong)b32[19] << 32 | (ulong)b32[18] << 40 | (ulong)b32[17] << 48 | (ulong)b32[16] << 56;
    r->d[2] = (ulong)b32[15] | (ulong)b32[14] << 8 | (ulong)b32[13] << 16 | (ulong)b32[12] << 24 | (ulong)b32[11] << 32 | (ulong)b32[10] << 40 | (ulong)b32[9]  << 48 | (ulong)b32[8]  << 56;
    r->d[3] = (ulong)b32[7]  | (ulong)b32[6]  << 8 | (ulong)b32[5]  << 16 | (ulong)b32[4]  << 24 | (ulong)b32[3]  << 32 | (ulong)b32[2]  << 40 | (ulong)b32[1]  << 48 | (ulong)b32[0]  << 56;
    over = secp256k1_scalar_reduce(r, secp256k1_scalar_check_overflow(r));
    if (overflow) {
        *overflow = over;
    }
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

/* Compute (t/2^62) * [d, e] mod modulus, where t is a transition matrix scaled by 2^62.
 *
 * On input and output, d and e are in range (-2*modulus,modulus). All output limbs will be in range
 * (-2^62,2^62).
 *
 * This implements the update_de function from the explanation.
 */
static void secp256k1_modinv64_update_de_62(secp256k1_modinv64_signed62 *d, secp256k1_modinv64_signed62 *e, const secp256k1_modinv64_trans2x2 *t, const secp256k1_modinv64_modinfo* modinfo) {
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
    VERIFY_CHECK((secp256k1_i128_to_u64(&cd) & M62) == 0); secp256k1_i128_rshift(&cd, 62);
    VERIFY_CHECK((secp256k1_i128_to_u64(&ce) & M62) == 0); secp256k1_i128_rshift(&ce, 62);
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

/* Determine the number of trailing zero bits in a (non-zero) 64-bit x.
 * This function is only intended to be used as fallback for
 * secp256k1_ctz64_var, but permits it to be tested separately. */
static int secp256k1_ctz64_var_debruijn(ulong x) {
    const uchar debruijn[64] = {
        0, 1, 2, 53, 3, 7, 54, 27, 4, 38, 41, 8, 34, 55, 48, 28,
        62, 5, 39, 46, 44, 42, 22, 9, 24, 35, 59, 56, 49, 18, 29, 11,
        63, 52, 6, 26, 37, 40, 33, 47, 61, 45, 43, 21, 23, 58, 17, 10,
        51, 25, 36, 32, 60, 20, 57, 16, 50, 31, 19, 15, 30, 14, 13, 12
    };
    return debruijn[(ulong)((x & -x) * 0x022FDD63CC95386DU) >> 58];
}

/* Compute the transition matrix and eta for 62 divsteps (variable time, eta=-delta).
 *
 * Input:  eta: initial eta
 *         f0:  bottom limb of initial f
 *         g0:  bottom limb of initial g
 * Output: t: transition matrix
 * Return: final eta
 *
 * Implements the divsteps_n_matrix_var function from the explanation.
 */
static ulong secp256k1_modinv64_divsteps_62_var(long eta, ulong f0, ulong g0, secp256k1_modinv64_trans2x2 *t) {
    /* Transformation matrix; see comments in secp256k1_modinv64_divsteps_62. */
    ulong u = 1, v = 0, q = 0, r = 1;
    ulong f = f0, g = g0, m;
    ulong w;
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
            /* Find what multiple of f must be added to g to cancel its bottom min(limit, 6)
             * bits. */
            w = (f * g * (f * f - 2)) & m;
        } else {
            /* In this branch, use a simpler formula that only lets us cancel up to 4 bits of g, as
             * eta tends to be smaller here. */
            limit = ((int)eta + 1) > i ? i : ((int)eta + 1);
            /* m is a mask for the bottom min(limit, 4) bits. */
            m = (ULONG_MAX >> (64 - limit)) & 15U;
            /* Find what multiple of f must be added to g to cancel its bottom min(limit, 4)
             * bits. */
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

// NEEDS WORK

/* Compute the inverse of x modulo modinfo->modulus, and replace x with it (variable time). */
static void secp256k1_modinv64_var(secp256k1_modinv64_signed62 *x, const secp256k1_modinv64_modinfo *modinfo) {
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
        cond = ((int64_t)len - 2) >> 63;
        cond |= fn ^ (fn >> 63);
        cond |= gn ^ (gn >> 63);
        /* If so, reduce length, propagating the sign of f and g's top limb into the one below. */
        if (cond == 0) {
            f.v[len - 2] |= (ulong)fn << 62;
            g.v[len - 2] |= (ulong)gn << 62;
            --len;
        }
#ifdef VERIFY
        VERIFY_CHECK(++i < 12); /* We should never need more than 12*62 = 744 divsteps */
        VERIFY_CHECK(secp256k1_modinv64_mul_cmp_62(&f, len, &modinfo->modulus, -1) > 0); /* f > -modulus */
        VERIFY_CHECK(secp256k1_modinv64_mul_cmp_62(&f, len, &modinfo->modulus, 1) <= 0); /* f <= modulus */
        VERIFY_CHECK(secp256k1_modinv64_mul_cmp_62(&g, len, &modinfo->modulus, -1) > 0); /* g > -modulus */
        VERIFY_CHECK(secp256k1_modinv64_mul_cmp_62(&g, len, &modinfo->modulus, 1) < 0);  /* g <  modulus */
#endif
    }

    /* At this point g is 0 and (if g was not originally 0) f must now equal +/- GCD of
     * the initial f, g values i.e. +/- 1, and d now contains +/- the modular inverse. */
#ifdef VERIFY
    /* g == 0 */
    VERIFY_CHECK(secp256k1_modinv64_mul_cmp_62(&g, len, &SECP256K1_SIGNED62_ONE, 0) == 0);
    /* |f| == 1, or (x == 0 and d == 0 and |f|=modulus) */
    VERIFY_CHECK(secp256k1_modinv64_mul_cmp_62(&f, len, &SECP256K1_SIGNED62_ONE, -1) == 0 ||
                 secp256k1_modinv64_mul_cmp_62(&f, len, &SECP256K1_SIGNED62_ONE, 1) == 0 ||
                 (secp256k1_modinv64_mul_cmp_62(x, 5, &SECP256K1_SIGNED62_ONE, 0) == 0 &&
                  secp256k1_modinv64_mul_cmp_62(&d, 5, &SECP256K1_SIGNED62_ONE, 0) == 0 &&
                  (secp256k1_modinv64_mul_cmp_62(&f, len, &modinfo->modulus, 1) == 0 ||
                   secp256k1_modinv64_mul_cmp_62(&f, len, &modinfo->modulus, -1) == 0)));
#endif

    /* Optionally negate d, normalize to [0,modulus), and return it. */
    secp256k1_modinv64_normalize_62(&d, f.v[len - 1], modinfo);
    *x = d;
}

static void secp256k1_scalar_inverse_var(secp256k1_scalar *r, const secp256k1_scalar *x) {
    secp256k1_modinv64_signed62 s;

    secp256k1_scalar_to_signed62(&s, x);
    secp256k1_modinv64_var(&s, &secp256k1_const_modinfo_scalar);
    secp256k1_scalar_from_signed62(r, &s);
}

// TODO: Removed const from 'sig'... check to see if this is ok
static void secp256k1_ecdsa_signature_load(const secp256k1_context* ctx, secp256k1_scalar* r, secp256k1_scalar* s, secp256k1_ecdsa_signature* sig) {
    (void)ctx;
    if (sizeof(secp256k1_scalar) == 32) {
        /* When the secp256k1_scalar type is exactly 32 byte, use its
         * representation inside secp256k1_ecdsa_signature, as conversion is very fast.
         * Note that secp256k1_ecdsa_signature_save must use the same representation. */
        memcpy_opencl((uchar*)r, &sig->data[0], 32);
        memcpy_opencl((uchar*)s, &sig->data[32], 32);
    } else {
        secp256k1_scalar_set_b32(r, &sig->data[0], 0);
        secp256k1_scalar_set_b32(s, &sig->data[32], 0);
    }
}

// TODO: No pubkey const
static int secp256k1_pubkey_load(const secp256k1_context* ctx, secp256k1_ge* ge, secp256k1_pubkey* pubkey) {
    if (sizeof(secp256k1_ge_storage) == 64) {
        /* When the secp256k1_ge_storage type is exactly 64 byte, use its
         * representation inside secp256k1_pubkey, as conversion is very fast.
         * Note that secp256k1_pubkey_save must use the same representation. */
        secp256k1_ge_storage s;

		// TODO: Check memcpy with OpenCl structures
        memcpy_opencl((uchar*)&s, &pubkey->data[0], sizeof(s));
        secp256k1_ge_from_storage(ge, &s);
    } else {
        /* Otherwise, fall back to 32-byte big endian for X and Y. */
        secp256k1_fe x, y;
        secp256k1_fe_set_b32_mod(&x, pubkey->data);
        secp256k1_fe_set_b32_mod(&y, pubkey->data + 32);
        secp256k1_ge_set_xy(ge, &x, &y);
    }
    
	// TODO: No Verify
	//ARG_CHECK(!secp256k1_fe_is_zero(&ge->x));
    return 1;
}

static int secp256k1_ecdsa_sig_verify(const secp256k1_scalar *sigr, const secp256k1_scalar *sigs, const secp256k1_ge *pubkey, const secp256k1_scalar *message) {
    unsigned char c[32];
    secp256k1_scalar sn, u1, u2;

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
    if (secp256k1_fe_cmp_var(&xr, &secp256k1_ecdsa_const_p_minus_order) >= 0) {
        /* xr + n >= p, so we can skip testing the second case. */
        return 0;
    }
    secp256k1_fe_add(&xr, &secp256k1_ecdsa_const_order_as_fe);
    if (secp256k1_gej_eq_x_var(&xr, &pr)) {
        /* (xr + n) * pr.z^2 mod p == pr.x, so the signature is valid. */
        return 1;
    }
    return 0;
}

int secp256k1_ecdsa_verify(const secp256k1_context* ctx, secp256k1_ecdsa_signature *sig, const unsigned char *msghash32, const secp256k1_pubkey *pubkey);

// TODO: Removed const from 'sig'... check to see if this is ok
int secp256k1_ecdsa_verify(const secp256k1_context* ctx, secp256k1_ecdsa_signature *sig, const unsigned char *msghash32, const secp256k1_pubkey *pubkey) {
    secp256k1_ge q;
    secp256k1_scalar r, s;
    secp256k1_scalar m;

    secp256k1_scalar_set_b32(&m, msghash32, 0);

    secp256k1_ecdsa_signature_load(ctx, &r, &s, sig);
    return (!secp256k1_scalar_is_high(&s) &&
            secp256k1_pubkey_load(ctx, &q, pubkey) &&
            secp256k1_ecdsa_sig_verify(&r, &s, &q, &m));
}


__kernel void secp256k1_verify( __global uchar*   input,
	                            __global uchar*   output) {
	int x = get_global_id(0);       // x
	int y = get_global_id(1);       // y
	int z = get_global_id(2);       // z
	int w = get_global_size(0);     // x.length (width)
	int h = get_global_size(1);     // y.length (height)

	secp256k1_scalar s;

}