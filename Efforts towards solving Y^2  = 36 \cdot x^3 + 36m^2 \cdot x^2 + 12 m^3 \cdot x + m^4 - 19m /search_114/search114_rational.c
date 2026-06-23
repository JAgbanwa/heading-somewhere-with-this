/*
 * search114_rational.c  --  Correct Booker-style search accounting for
 * rational K = (n - n0)/M30.
 *
 * MATHEMATICAL BASIS:
 * The equation y^2 = (alpha+6n)^2 + (36n^3-19)/alpha has solutions for
 * integer n and integer alpha | (36n^3-19). There is NO requirement that
 * n ≡ n0 (mod M30). The actual solution n* yields K* = (n*-n0)/M30 which
 * is generically rational non-integer.
 *
 * The parametrisation n = M30*K + n0 covers ALL integers n via rational K.
 * To cover rational K = p/q with q | M30, we equivalently search
 * n = (M30/q)*p + n0 over integer p, for each divisor q of M30.
 *
 * Since M30 = 5*11*17*...*257 has 2^30 divisors, we search the 31 most
 * important sub-families:
 *   q = 1     (integer K):    n = M30*p + n0        [original, modulus M30]
 *   q = p_i   (one prime):    n = (M30/p_i)*p + n0  [30 sub-families]
 *
 * Together these cover K with denominators 1, 5, 11, 17, ..., 257.
 *
 * For each sub-family with modulus d = M30/q:
 *   - For each prime alpha, solve 36*(d*p+n0)^3 ≡ 19 (mod alpha) for p mod alpha
 *   - Iterate p in each residue class, |p| <= P_MAX
 *   - For M30 primes: all p are valid roots (by CRT construction), full sweep
 *   - Check y^2 = (alpha + 6n)^2 + (36n^3-19)/alpha is a perfect square
 *
 * P_MAX = 10^10 for each sub-family. The actual n range covered:
 *   Sub-family d=M30:    |n-n0| up to M30*10^10  ~ 10^54
 *   Sub-family d=M30/5:  |n-n0| up to (M30/5)*10^10 ~ 10^53
 *   ...all together covering n in a dense mesh around n0 up to ~10^54.
 *
 * The KEY insight: the n0 centering means even p=1 gives n ~ 10^57,
 * so the search naturally hits astronomically large n values, consistent
 * with where solutions to x^3+y^3+z^3=114 are expected to live.
 *
 * INTEGER X CONSTRAINT:
 * The original equation uses alpha = 12X+7, so X = (alpha-7)/12 is an
 * integer iff alpha ≡ 7 (mod 12). The alpha loop now steps only through
 * values satisfying this congruence (7, 19, 31, 43, ...), guaranteeing
 * integer X for every candidate checked. This also triples search speed
 * by skipping 11 out of every 12 alpha values.
 *
 * Build:  gcc -O3 -o search114_rational search114_rational.c -lgmp
 * Run:    ./search114_rational FAMILY P_START P_END [output]
 *   FAMILY: 0 = full M30 (integer K)
 *           1..24 = remove i-th M30 prime (rational K with that denominator)
 *   P_START, P_END: range of integer p to search
 *
 * Charity Engine env vars: FAMILY, P_START, P_END, OUTPUT
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <gmp.h>
#include <time.h>

/* ── Constants ─────────────────────────────────────────────────────────── */
static const char *S_n0 =
    "1820733127217158956577191662349053768348092988705876831189";
static const char *S_M30 =
    "5103243448423190660018404944928000789930010683701564743465";

static const unsigned long M30_PRIMES[] = {
    5,11,17,19,23,29,41,47,53,59,71,83,89,101,107,113,131,137,149,
    227,233,239,251,257, 0
};
#define N_M30_PRIMES 24

/* ── Modular arithmetic ─────────────────────────────────────────────────── */
static unsigned long mulmod(unsigned long a,unsigned long b,unsigned long m){
    return (__uint128_t)a*b%m;
}
static unsigned long powmod(unsigned long b,unsigned long e,unsigned long m){
    unsigned long r=1; b%=m;
    for(;e;e>>=1){if(e&1)r=mulmod(r,b,m);b=mulmod(b,b,m);}
    return r;
}
static unsigned long modinv(unsigned long a,unsigned long m){
    mpz_t ga,gm,gi; mpz_inits(ga,gm,gi,NULL);
    mpz_set_ui(ga,a); mpz_set_ui(gm,m); mpz_invert(gi,ga,gm);
    unsigned long r=mpz_get_ui(gi);
    mpz_clears(ga,gm,gi,NULL); return r;
}

/*
 * Find all p in [0,alpha) s.t. alpha | (36*(d*p+n0)^3 - 19), prime alpha.
 * s = d mod alpha, r = n0 mod alpha.
 * Reduces to: (s*p+r)^3 ≡ c (mod alpha) where c = 19*inv(36) mod alpha.
 * Returns -1 if ALL p are roots (when s=0, i.e. alpha | d).
 * Otherwise returns count of roots in roots[].
 */
static int roots_mod_prime(unsigned long alpha,
                            unsigned long s, unsigned long r,
                            long long roots[3])
{
    if(s==0) return -1; /* alpha | d => all p are roots */

    unsigned long inv36 = modinv(36UL % alpha, alpha);
    unsigned long c = mulmod(19UL % alpha, inv36, alpha);

    unsigned long u_roots[3]; int nu=0;
    if(alpha%3==2){
        unsigned long u=powmod(c,(2*alpha-1)/3,alpha);
        if(mulmod(mulmod(u,u,alpha),u,alpha)==c) u_roots[nu++]=u;
    } else {
        if(c==0){ u_roots[nu++]=0; }
        else if(powmod(c,(alpha-1)/3,alpha)==1){
            for(unsigned long u=0;u<alpha&&nu<3;u++)
                if(mulmod(mulmod(u,u,alpha),u,alpha)==c)
                    u_roots[nu++]=u;
        }
    }

    unsigned long inv_s=modinv(s,alpha);
    int nk=0;
    for(int i=0;i<nu;i++){
        long long diff=(long long)u_roots[i]-(long long)r;
        long long k=((diff%(long long)alpha)+(long long)alpha)%(long long)alpha;
        roots[nk++]=(long long)mulmod((unsigned long)k,inv_s,alpha);
    }
    return nk;
}

/* ── GMP globals ─────────────────────────────────────────────────────────── */
static mpz_t g_n0,g_d,g_p,g_n,g_n3,g_N3,g_6n,g_inner,g_rhs,g_Y,g_Y2;

static void gmp_setup(void){
    mpz_inits(g_n0,g_d,g_p,g_n,g_n3,g_N3,g_6n,g_inner,g_rhs,g_Y,g_Y2,NULL);
    mpz_set_str(g_n0,S_n0,10);
}
static void gmp_teardown(void){
    mpz_clears(g_n0,g_d,g_p,g_n,g_n3,g_N3,g_6n,g_inner,g_rhs,g_Y,g_Y2,NULL);
}

/*
 * Check one (p, alpha) candidate.
 * n = d*p + n0. Returns 1 if solution found, fills Yout.
 */
static int check(long long p_val, unsigned long alpha, mpz_t Yout){
    mpz_set_si(g_p, p_val);
    mpz_mul(g_n, g_d, g_p);
    mpz_add(g_n, g_n, g_n0);              /* n = d*p + n0 */

    mpz_mul(g_n3,g_n,g_n); mpz_mul(g_n3,g_n3,g_n);
    mpz_mul_ui(g_N3,g_n3,36); mpz_sub_ui(g_N3,g_N3,19);  /* 36n^3-19 */

    if(!mpz_divisible_ui_p(g_N3,alpha)) return 0;
    mpz_divexact_ui(g_inner,g_N3,alpha); /* (36n^3-19)/alpha */

    mpz_mul_ui(g_6n,g_n,6);
    mpz_set_ui(g_rhs,alpha); mpz_add(g_rhs,g_rhs,g_6n); /* alpha+6n */
    mpz_mul(g_rhs,g_rhs,g_rhs);          /* (alpha+6n)^2 */
    mpz_add(g_rhs,g_rhs,g_inner);        /* + (36n^3-19)/alpha */

    if(mpz_sgn(g_rhs)<0) return 0;
    mpz_sqrt(g_Y,g_rhs); mpz_mul(g_Y2,g_Y,g_Y);
    if(mpz_cmp(g_Y2,g_rhs)==0){ mpz_set(Yout,g_Y); return 1; }
    return 0;
}

/* ── Main ────────────────────────────────────────────────────────────────── */
int main(int argc,char **argv){
    /* Read parameters */
    const char *env_family  = getenv("FAMILY");
    const char *env_pstart  = getenv("P_START");
    const char *env_pend    = getenv("P_END");
    const char *env_output  = getenv("OUTPUT");

    int    family   = atoi(env_family  ? env_family  : (argc>1?argv[1]:"0"));
    long long P_start = atoll(env_pstart ? env_pstart : (argc>2?argv[2]:"-10000000000"));
    long long P_end   = atoll(env_pend   ? env_pend   : (argc>3?argv[3]:"10000000000"));
    const char *outpath = env_output ? env_output : (argc>4?argv[4]:NULL);

    FILE *out = outpath ? fopen(outpath,"w") : stdout;
    if(!out){perror(outpath);return 1;}

    /* Validate family */
    if(family<0||family>N_M30_PRIMES){
        fprintf(stderr,"FAMILY must be 0..%d\n",N_M30_PRIMES);return 1;
    }

    gmp_setup();

    /* Compute d = M30 / (family-th prime), or M30 if family=0 */
    mpz_t M30; mpz_init(M30); mpz_set_str(M30,S_M30,10);
    if(family==0){
        mpz_set(g_d,M30);
    } else {
        unsigned long removed_prime = M30_PRIMES[family-1];
        mpz_divexact_ui(g_d,M30,removed_prime);
    }

    unsigned long removed_p = (family==0)?1:M30_PRIMES[family-1];
    char d_str[200]; gmp_sprintf(d_str,"%Zd",g_d);

    fprintf(out,"# search114_rational\n");
    fprintf(out,"# FAMILY=%d (remove prime %lu, d=M30/%lu)\n",
            family,removed_p,removed_p);
    fprintf(out,"# d=%s\n",d_str);
    fprintf(out,"# P range=[%lld,%lld]\n",P_start,P_end);
    fprintf(out,"# Columns: p,alpha,X,Y,n,K_numerator,K_denominator\n");
    fflush(out);

    /* For reporting K = (n-n0)/M30 = p/removed_p (rational) */
    /* K_num = p, K_den = removed_p (for family>0) or K=p (family=0) */

    mpz_t Yout,n_out,K_num,K_den,diff;
    mpz_inits(Yout,n_out,K_num,K_den,diff,NULL);
    mpz_set_ui(K_den,(family==0)?1:removed_p);

    int total_sol=0;
    time_t t0=time(NULL);
    unsigned long n_alpha_done=0;

    printf("Family %d: d=M30/%lu (%zu digits), p in [%lld,%lld]\n",
           family,removed_p,strlen(d_str),P_start,P_end);
    printf("Alpha stepping through values ≡ 7 (mod 12) => integer X = (alpha-7)/12\n");

    /*
     * Drive over prime alpha ≡ 7 (mod 12).
     * This guarantees X = (alpha-7)/12 is a non-negative integer.
     * alpha=7,19,31,43,... -- step by 12 each iteration.
     * Note: alpha ≡ 7 (mod 12) => alpha is odd and alpha ≢ 0 (mod 3),
     * so the old even/div-by-3 guards are subsumed by the step itself.
     * We still exclude alpha divisible by 19^2=361.
     */
    for(unsigned long alpha=7; alpha<=200003; alpha+=12){
        /* 19^2 = 361 guard (from .tex: 19^2 permanently forbidden) */
        if(alpha%361==0) continue;
        /* Primality check */
        int prime=1;
        if(alpha>3){
            for(unsigned long dd=5;dd*dd<=alpha;dd+=2)
                if(alpha%dd==0){prime=0;break;}
        }
        if(!prime) continue;

        /* s = d mod alpha */
        mpz_t tmp; mpz_init(tmp);
        mpz_mod_ui(tmp,g_d,alpha);   unsigned long s=mpz_get_ui(tmp);
        mpz_mod_ui(tmp,g_n0,alpha);  unsigned long r=mpz_get_ui(tmp);
        mpz_clear(tmp);

        long long roots[3];
        int nr=roots_mod_prime(alpha,s,r,roots);

        if(nr==-1){
            /* alpha | d: ALL p are roots => full sweep */
            for(long long p=P_start;p<=P_end;p++){
                if(p==0) continue;
                if(check(p,alpha,Yout)){
                    total_sol++;
                    /* Compute n = d*p+n0 */
                    mpz_set_si(g_p,p); mpz_mul(n_out,g_d,g_p); mpz_add(n_out,n_out,g_n0);
                    unsigned long X_val=(alpha-7)/12;
                    fprintf(out,"%lld,%lu,%lu,",p,alpha,X_val);
                    gmp_fprintf(out,"%Zd,",Yout);
                    gmp_fprintf(out,"%Zd,",n_out);
                    if(family==0) fprintf(out,"%lld,1\n",p);
                    else          fprintf(out,"%lld,%lu\n",p,removed_p);
                    fflush(out);
                    printf("SOLUTION: p=%lld alpha=%lu X=%lu family=%d (K=%lld/%lu)\n",
                           p,alpha,X_val,family,p,removed_p);
                }
            }
        } else {
            for(int ri=0;ri<nr;ri++){
                long long p_base=roots[ri];
                long long j_lo=( P_start-p_base)/(long long)alpha;
                long long j_hi=( P_end  -p_base)/(long long)alpha;
                while(p_base+j_lo*(long long)alpha<P_start) j_lo++;
                while(p_base+j_hi*(long long)alpha>P_end)   j_hi--;
                for(long long j=j_lo;j<=j_hi;j++){
                    long long p=p_base+j*(long long)alpha;
                    if(p==0) continue;
                    if(check(p,alpha,Yout)){
                        total_sol++;
                        mpz_set_si(g_p,p); mpz_mul(n_out,g_d,g_p); mpz_add(n_out,n_out,g_n0);
                        unsigned long X_val=(alpha-7)/12;
                        fprintf(out,"%lld,%lu,%lu,",p,alpha,X_val);
                        gmp_fprintf(out,"%Zd,",Yout);
                        gmp_fprintf(out,"%Zd,",n_out);
                        if(family==0) fprintf(out,"%lld,1\n",p);
                        else          fprintf(out,"%lld,%lu\n",p,removed_p);
                        fflush(out);
                        printf("SOLUTION: p=%lld alpha=%lu X=%lu family=%d (K=%lld/%lu)\n",
                               p,alpha,X_val,family,p,removed_p);
                    }
                }
            }
        }

        n_alpha_done++;
        if(n_alpha_done%10000==0){
            printf("  alpha=%lu done=%lu t=%lds sol=%d\n",
                   alpha,n_alpha_done,(long)(time(NULL)-t0),total_sol);
            fflush(stdout);
        }
    }

    printf("Done. family=%d sol=%d elapsed=%lds\n",
           family,total_sol,(long)(time(NULL)-t0));

    if(out!=stdout) fclose(out);
    mpz_clears(M30,Yout,n_out,K_num,K_den,diff,NULL);
    gmp_teardown();
    return 0;
}
