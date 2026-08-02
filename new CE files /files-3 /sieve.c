/* sieve.c — congruence sieve for   y^2 = (6n + x)^2 + (36 n^3 - k)/x   (default k = 19)
 *
 * Mathematical basis
 * ------------------
 * Multiply by x:  x*y^2 = x*(x+6n)^2 + N,  N = 36 n^3 - k.
 * With u = y - x - 6n, v = y + x + 6n this is the 3-factor identity
 *       x * u * v = N,   v - u = 2(x + 6n).
 * For k = 19: N is odd and N == 2 (mod 3), so every divisor of N is coprime to 6.
 * For n >> |m| one shows easily:
 *   - x < 0 with |x| small is impossible  ( (6n-|x|)^2 < N/|x| )
 *   - u < 0 with |u| small is impossible  (same size argument)
 *   - v small is impossible               ( v = u + 2x + 12n >= ~12n )
 * Hence every solution with a "small" factor has either small x>0 or small u>0.
 *
 * Two sieve branches, both driven by the same congruence 36 r^3 == k (mod m):
 *   X-branch (m = x):  n == r (mod x);  T(n) = (x+6n)^2 + (36n^3-k)/x  must be a square (=> y).
 *   U-branch (m = u):  n == r (mod u);  D(n) = (u+12n)^2 + 8(36n^3-k)/u must be a square s^2,
 *                      then x = (s - u - 12n)/4 must be a positive integer, y = x + 6n + u.
 *                      (from 2x^2 + (u+12n)x - N/u = 0; reaches x ~ sqrt(N/2u), i.e. huge x.)
 *
 * For each modulus m the residues r are the roots of 36 r^3 - k (mod m), computed via
 * factorization of m, cube roots mod p (AMM for p == 1 mod 3), naive Hensel lifting to p^e,
 * and CRT. Scanning a class uses cubic finite differences: 3 big-int adds per candidate,
 * a mod-256 square filter, then mpz_perfect_square_p.
 *
 * Coverage guarantee per finished chunk: ALL solutions with n in the chunk and
 * (x <= xmax  OR  y - x - 6n <= umax). Solutions where x, u, v are ALL large are not
 * reachable without factoring N (60-120 digit numbers) — no method covers those at scale.
 *
 * Build:   gcc -O3 -march=native -o sieve sieve.c -lgmp
 * Static (Charity Engine): gcc -O3 -static -o sieve sieve.c -lgmp
 *
 * Usage examples:
 *   ./sieve --selftest
 *   ./sieve --n0 10^20 --len 10^11 --xmax 10^6 --umax 10^6 --time 3600
 *   ./sieve --n0 10^30 --len 10^11 --xmax 10^6 --umax 10^6 --time 3600
 *   sharding:  --shard I --nshards T   (task I of T scans an equal slice of [n0,n1))
 * Numbers accept forms: 123456, 10^20, 3e15.
 */
#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <gmp.h>

typedef uint64_t u64;
typedef int64_t  i64;
typedef unsigned __int128 u128;
typedef uint32_t u32;

#define MAXR 243            /* cap on residues per modulus */
#define PRIME_LIMIT 65536   /* factor m up to 65536^2 ~ 4.29e9 */

static u32 *primes; static int nprimes;
static unsigned char sq256[256];

static void build_primes(void){
    static unsigned char comp[PRIME_LIMIT];
    for (int i=2;i<PRIME_LIMIT;i++)
        if(!comp[i]) for(long j=(long)i*i;j<PRIME_LIMIT;j+=i) comp[j]=1;
    int c=0; for(int i=2;i<PRIME_LIMIT;i++) if(!comp[i]) c++;
    primes=malloc(c*sizeof(u32)); nprimes=0;
    for(int i=2;i<PRIME_LIMIT;i++) if(!comp[i]) primes[nprimes++]=i;
}

static inline u64 mulmod(u64 a,u64 b,u64 m){ return (u64)(((u128)a*b)%m); }
static u64 powmod(u64 a,u64 e,u64 m){
    u64 r = 1%m; a%=m;
    while(e){ if(e&1) r=mulmod(r,a,m); a=mulmod(a,a,m); e>>=1; }
    return r;
}
static u64 invmod(u64 a,u64 m){            /* gcd(a,m)=1, m < 2^63 */
    i64 t=0,nt=1,r=(i64)m,nr=(i64)(a%m);
    while(nr){ i64 q=r/nr,tmp;
        tmp=t-q*nt; t=nt; nt=tmp;
        tmp=r-q*nr; r=nr; nr=tmp; }
    return (u64)(t<0? t+(i64)m : t);
}

/* roots of r^3 == c (mod p), p prime >= 5, gcd(p,6)=1. returns count (0,1,3). */
static int cbrt_modp(u64 c,u64 p,u64 out[3]){
    c%=p;
    if(c==0){ out[0]=0; return 1; }
    if(p%3==2){ out[0]=powmod(c,(2*p-1)/3,p); return 1; }
    if(powmod(c,(p-1)/3,p)!=1) return 0;                 /* not a cubic residue */
    u64 t=p-1; int s=0; while(t%3==0){t/=3;s++;}
    u64 g=2; while(powmod(g,(p-1)/3,p)==1) g++;
    u64 K=powmod(g,t,p);                                  /* order 3^s */
    u64 alpha=invmod(3%t,t);
    u64 y=powmod(c,alpha,p);
    u64 z=mulmod(mulmod(y,y,p),y,p);
    z=mulmod(z,powmod(c,p-2,p),p);                        /* z = y^3/c in Sylow-3 */
    u64 pw3[41]; pw3[0]=1; for(int i=1;i<=s;i++) pw3[i]=pw3[i-1]*3;
    u64 W=powmod(K,pw3[s-1],p), Kinv=powmod(K,p-2,p);
    u64 j=0,zz=z;
    for(int i=0;i<s;i++){
        u64 w=powmod(zz,pw3[s-1-i],p);
        u64 d = (w==1)?0 : (w==W)?1 : 2;
        if(d){ j+=d*pw3[i]; zz=mulmod(zz,powmod(Kinv,d*pw3[i],p),p); }
    }
    if(j%3) return 0;                                     /* cannot happen for residues */
    u64 x0=mulmod(y,powmod(powmod(K,j/3,p),p-2,p),p);
    out[0]=x0; out[1]=mulmod(x0,W,p); out[2]=mulmod(x0,mulmod(W,W,p),p);
    return 3;
}

/* roots of f(r)=36 r^3 - k == 0 (mod p) */
static int froots_modp(i64 k,u64 p,u64 out[3]){
    if(p<=3){
        int c=0; u64 kk=(u64)(((k%(i64)p)+(i64)p)%(i64)p);
        for(u64 r=0;r<p;r++){
            u64 v=((36%p)*r%p)*r%p*r%p;
            if((v+p-kk)%p==0) out[c++]=r;
        }
        return c;
    }
    u64 kk=(u64)(((k%(i64)p)+(i64)p)%(i64)p);
    u64 c=mulmod(kk,powmod(36%p,p-2,p),p);
    return cbrt_modp(c,p,out);
}

/* roots mod p^e via naive lifting; returns count, 0 if none, -1 if > MAXR */
static int froots_modpe(i64 k,u64 p,int e,u64 *out){
    u64 cur[MAXR],nxt[MAXR];
    int cc=froots_modp(k,p,cur);
    if(cc<=0) return cc;
    u64 q=p;
    for(int lvl=1;lvl<e;lvl++){
        u64 q2=q*p; int nc=0;
        u64 kk=(u64)(((k%(i64)q2)+(i64)q2)%(i64)q2);
        for(int a=0;a<cc;a++)
            for(u64 j=0;j<p;j++){
                u64 cand=cur[a]+j*q;
                u64 v=mulmod(mulmod(mulmod(36%q2,cand,q2),cand,q2),cand,q2);
                if((v+q2-kk)%q2==0){
                    if(nc>=MAXR) return -1;
                    nxt[nc++]=cand;
                }
            }
        if(!nc) return 0;
        memcpy(cur,nxt,nc*sizeof(u64)); cc=nc; q=q2;
    }
    memcpy(out,cur,cc*sizeof(u64));
    return cc;
}

static int factorize(u64 m,u64 pf[16],int ef[16]){
    int np=0;
    for(int i=0;i<nprimes && (u64)primes[i]*primes[i]<=m;i++){
        u64 p=primes[i];
        if(m%p==0){ pf[np]=p; ef[np]=0; while(m%p==0){m/=p; ef[np]++;} np++; }
    }
    if(m>1){ pf[np]=m; ef[np]=1; np++; }
    return np;
}

/* all roots of 36 r^3 == k (mod m). returns count, 0 none, -1 too many */
static int froots_modm(i64 k,u64 m,u64 *out){
    if(m==1){ out[0]=0; return 1; }
    u64 pf[16]; int ef[16];
    int np=factorize(m,pf,ef);
    u64 cur[MAXR],nxt[MAXR],rq[MAXR];
    int rc=1; cur[0]=0; u64 mod=1;
    for(int i=0;i<np;i++){
        u64 q=1; for(int e=0;e<ef[i];e++) q*=pf[i];
        int qc=froots_modpe(k,pf[i],ef[i],rq);
        if(qc<=0) return qc;
        if((long)rc*qc>MAXR) return -1;
        u64 inv=invmod(mod%q,q); int nc=0;
        for(int a=0;a<rc;a++)
            for(int b=0;b<qc;b++){
                u64 diff=(rq[b]+q-cur[a]%q)%q;
                nxt[nc++]=cur[a]+mod*mulmod(diff,inv,q);
            }
        memcpy(cur,nxt,nc*sizeof(u64)); rc=nc; mod*=q;
    }
    memcpy(out,cur,rc*sizeof(u64));
    return rc;
}

/* ---------------- scanning ---------------- */

typedef struct {
    mpz_t nn0,t0,t1,t2,t3,d1,d2,d3,ta,tb,hn,fresh,y,s,w,xx,N,q,chk,yy,tmp;
} Scratch;

static u64 g_cand=0, g_hits=0;
static double g_deadline; static int g_timeout=0;
static double now_sec(void){ struct timespec ts; clock_gettime(CLOCK_MONOTONIC,&ts);
    return ts.tv_sec+1e-9*ts.tv_nsec; }

/* T(n): branch 0 (X):  (m+6n)^2 +   (36n^3-k)/m
 *       branch 1 (U):  (m+12n)^2 + 8(36n^3-k)/m        (exact division guaranteed by class) */
static void eval_T(mpz_t out,const mpz_t n,u64 m,i64 k,int branch,mpz_t ta,mpz_t tb){
    mpz_mul(ta,n,n); mpz_mul(ta,ta,n); mpz_mul_ui(out,ta,36);
    if(k>=0) mpz_sub_ui(out,out,(u64)k); else mpz_add_ui(out,out,(u64)(-k));
    mpz_divexact_ui(out,out,m);
    if(branch) mpz_mul_2exp(out,out,3);
    mpz_mul_ui(tb,n,branch?12:6); mpz_add_ui(tb,tb,m);
    mpz_addmul(out,tb,tb);
}

static inline int sqcand(const mpz_t t){
    if(mpz_sgn(t)<0) return 0;
    if(!sq256[(unsigned)(mpz_getlimbn(t,0)&0xFF)]) return 0;
    return mpz_perfect_square_p(t);
}

static void handle_hit(int branch,u64 m,const mpz_t hn,const mpz_t tval,i64 k,Scratch*S){
    eval_T(S->fresh,hn,m,k,branch,S->ta,S->tb);
    if(mpz_cmp(S->fresh,tval)!=0)
        gmp_fprintf(stderr,"WARN: finite-difference drift at m=%llu n=%Zd\n",
                    (unsigned long long)m,hn);
    if(!mpz_perfect_square_p(S->fresh)) return;
    if(branch==0){
        mpz_sqrt(S->y,S->fresh);
        gmp_printf("SOLUTION  n=%Zd  x=%llu  y=%Zd   [x-branch]\n",
                   hn,(unsigned long long)m,S->y);
        g_hits++;
    }else{
        mpz_sqrt(S->s,S->fresh);
        mpz_mul_ui(S->ta,hn,12); mpz_add_ui(S->ta,S->ta,m);
        mpz_sub(S->w,S->s,S->ta);                 /* w = s - u - 12n = 4x */
        if(mpz_sgn(S->w)>0 && mpz_fdiv_ui(S->w,4)==0){
            mpz_divexact_ui(S->xx,S->w,4);
            mpz_mul_ui(S->tb,hn,6);
            mpz_add(S->y,S->xx,S->tb); mpz_add_ui(S->y,S->y,m);   /* y = x+6n+u */
            /* full independent verification */
            mpz_mul(S->tmp,hn,hn); mpz_mul(S->N,S->tmp,hn); mpz_mul_ui(S->N,S->N,36);
            if(k>=0) mpz_sub_ui(S->N,S->N,(u64)k); else mpz_add_ui(S->N,S->N,(u64)(-k));
            if(mpz_divisible_p(S->N,S->xx)){
                mpz_divexact(S->q,S->N,S->xx);
                mpz_add(S->chk,S->xx,S->tb);
                mpz_mul(S->chk,S->chk,S->chk); mpz_add(S->chk,S->chk,S->q);
                mpz_mul(S->yy,S->y,S->y);
                if(mpz_cmp(S->chk,S->yy)==0){
                    gmp_printf("SOLUTION  n=%Zd  x=%Zd  y=%Zd   [u-branch, u=%llu]\n",
                               hn,S->xx,S->y,(unsigned long long)m);
                    g_hits++;
                }
            }
        }
    }
    fflush(stdout);
}

static void scan_class(u64 m,u64 r,int branch,const mpz_t lo,const mpz_t hi,i64 k,Scratch*S){
    u64 rem=mpz_fdiv_ui(lo,m);
    u64 off=(r>=rem)? r-rem : r+m-rem;
    mpz_add_ui(S->nn0,lo,off);
    if(mpz_cmp(S->nn0,hi)>=0) return;
    mpz_sub(S->tmp,hi,S->nn0); mpz_sub_ui(S->tmp,S->tmp,1);
    mpz_fdiv_q_ui(S->tmp,S->tmp,m);
    u64 cnt=mpz_get_ui(S->tmp)+1;

    if(cnt<=4){
        mpz_set(S->hn,S->nn0);
        for(u64 i=0;i<cnt;i++){
            eval_T(S->t0,S->hn,m,k,branch,S->ta,S->tb);
            g_cand++;
            if(sqcand(S->t0)) handle_hit(branch,m,S->hn,S->t0,k,S);
            mpz_add_ui(S->hn,S->hn,m);
        }
        return;
    }
    /* finite differences with step m (third difference constant) */
    mpz_set(S->hn,S->nn0);
    eval_T(S->t0,S->hn,m,k,branch,S->ta,S->tb); mpz_add_ui(S->hn,S->hn,m);
    eval_T(S->t1,S->hn,m,k,branch,S->ta,S->tb); mpz_add_ui(S->hn,S->hn,m);
    eval_T(S->t2,S->hn,m,k,branch,S->ta,S->tb); mpz_add_ui(S->hn,S->hn,m);
    eval_T(S->t3,S->hn,m,k,branch,S->ta,S->tb);
    mpz_sub(S->d1,S->t1,S->t0);
    mpz_sub(S->d2,S->t2,S->t1); mpz_sub(S->tmp,S->t1,S->t0); mpz_sub(S->d2,S->d2,S->tmp);
    mpz_sub(S->ta,S->t3,S->t2); mpz_sub(S->tb,S->t2,S->t1); mpz_sub(S->ta,S->ta,S->tb);
    mpz_sub(S->d3,S->ta,S->d2);

    u64 kk=0;
    for(;;){
        g_cand++;
        if(sqcand(S->t0)){
            mpz_add_ui(S->hn,S->nn0,kk*m);
            handle_hit(branch,m,S->hn,S->t0,k,S);
        }
        if(++kk==cnt) break;
        mpz_add(S->t0,S->t0,S->d1);
        mpz_add(S->d1,S->d1,S->d2);
        mpz_add(S->d2,S->d2,S->d3);
        if((kk&0x3FFFFF)==0 && now_sec()>g_deadline){ g_timeout=1; return; }
    }
}

/* ---------------- selftest ---------------- */
static int selftest(void){
    int fail=0;
    /* cube-root machinery vs brute force */
    for(int pi=2;pi<nprimes && primes[pi]<1200;pi++){
        u64 p=primes[pi];
        for(u64 c=1;c<p && c<=40;c++){
            u64 br[3]; int bc=0;
            for(u64 r=0;r<p;r++) if(mulmod(mulmod(r,r,p),r,p)==c) br[bc++]=r;
            u64 ar[3]; int ac=cbrt_modp(c,p,ar);
            if(ac!=bc){ fail++; fprintf(stderr,"cbrt count mismatch p=%llu c=%llu\n",
                                        (unsigned long long)p,(unsigned long long)c); continue; }
            for(int i=0;i<ac;i++)
                if(mulmod(mulmod(ar[i],ar[i],p),ar[i],p)!=c){ fail++;
                    fprintf(stderr,"cbrt bad root p=%llu c=%llu\n",
                            (unsigned long long)p,(unsigned long long)c); }
        }
    }
    /* full root-finder vs brute force */
    i64 ks[4]={19,-212577,101,-3};
    for(int t=0;t<4;t++){
        i64 k=ks[t];
        for(u64 m=1;m<=2500;m++){
            unsigned char mark[2500]; memset(mark,0,m);
            for(u64 r=0;r<m;r++){
                u64 kk=(u64)(((k%(i64)m)+(i64)m)%(i64)m);
                u64 v=mulmod(mulmod(mulmod(36%m,r,m),r,m),r,m);
                if((v+m-kk)%m==0) mark[r]=1;
            }
            u64 out[MAXR]; int c=froots_modm(k,m,out);
            int bc=0; for(u64 r=0;r<m;r++) bc+=mark[r];
            if(c==-1){ if(bc<=MAXR){fail++; fprintf(stderr,"cap fail m=%llu\n",(unsigned long long)m);} continue; }
            if(c!=bc){ fail++; fprintf(stderr,"count mismatch k=%lld m=%llu got=%d want=%d\n",
                               (long long)k,(unsigned long long)m,c,bc); continue; }
            for(int i=0;i<c;i++) if(!mark[out[i]]){ fail++;
                fprintf(stderr,"bad root k=%lld m=%llu r=%llu\n",
                        (long long)k,(unsigned long long)m,(unsigned long long)out[i]); }
        }
    }
    printf(fail? "SELFTEST: %d FAILURES\n" : "SELFTEST: all passed\n", fail);
    return fail?1:0;
}

/* ---------------- misc ---------------- */
static void parse_big(mpz_t out,const char*s){
    const char *c;
    if((c=strchr(s,'^'))){
        char base[64]; size_t l=c-s; memcpy(base,s,l); base[l]=0;
        mpz_t b; mpz_init(b); mpz_set_str(b,base,10);
        mpz_pow_ui(out,b,strtoul(c+1,NULL,10)); mpz_clear(b);
    }else if((c=strchr(s,'e'))||(c=strchr(s,'E'))){
        char mant[64]; size_t l=c-s; memcpy(mant,s,l); mant[l]=0;
        mpz_set_str(out,mant,10);
        mpz_t p; mpz_init(p); mpz_ui_pow_ui(p,10,strtoul(c+1,NULL,10));
        mpz_mul(out,out,p); mpz_clear(p);
    }else mpz_set_str(out,s,10);
}
static u64 parse_u64(const char*s){
    mpz_t t; mpz_init(t); parse_big(t,s);
    u64 v=mpz_get_ui(t); mpz_clear(t); return v;
}

int main(int argc,char**argv){
    build_primes();
    for(int i=0;i<256;i++) sq256[(i*i)&0xFF]=1;

    mpz_t n0,n1,len,lo,hi; mpz_inits(n0,n1,len,lo,hi,NULL);
    mpz_set_ui(n0,1); mpz_set_ui(len,0); mpz_set_ui(n1,0);
    u64 xmax=1000000, umax=1000000, chunk=1000000000ULL;
    u64 shard=0, nshards=1;
    i64 k=19; double tlimit=3600; int do_selftest=0, have_n1=0, have_len=0;

    for(int i=1;i<argc;i++){
        if(!strcmp(argv[i],"--selftest")) do_selftest=1;
        else if(!strcmp(argv[i],"--n0")) parse_big(n0,argv[++i]);
        else if(!strcmp(argv[i],"--n1")){ parse_big(n1,argv[++i]); have_n1=1; }
        else if(!strcmp(argv[i],"--len")){ parse_big(len,argv[++i]); have_len=1; }
        else if(!strcmp(argv[i],"--xmax")) xmax=parse_u64(argv[++i]);
        else if(!strcmp(argv[i],"--umax")) umax=parse_u64(argv[++i]);
        else if(!strcmp(argv[i],"--chunk")) chunk=parse_u64(argv[++i]);
        else if(!strcmp(argv[i],"--k")) k=strtoll(argv[++i],NULL,10);
        else if(!strcmp(argv[i],"--time")) tlimit=atof(argv[++i]);
        else if(!strcmp(argv[i],"--shard")) shard=parse_u64(argv[++i]);
        else if(!strcmp(argv[i],"--nshards")) nshards=parse_u64(argv[++i]);
        else { fprintf(stderr,"unknown arg %s\n",argv[i]); return 2; }
    }
    if(do_selftest) return selftest();
    if(have_len && !have_n1) mpz_add(n1,n0,len);
    if(!have_len && !have_n1){ fprintf(stderr,"need --n1 or --len\n"); return 2; }
    if(nshards>1){                          /* task `shard` of `nshards` */
        mpz_t width,off; mpz_inits(width,off,NULL);
        mpz_sub(width,n1,n0); mpz_cdiv_q_ui(width,width,nshards);
        mpz_mul_ui(off,width,shard); mpz_add(n0,n0,off);
        mpz_add(off,n0,width); if(mpz_cmp(off,n1)<0) mpz_set(n1,off);
        mpz_clears(width,off,NULL);
    }
    u64 M = xmax>umax? xmax:umax;
    if(M>4200000000ULL){ fprintf(stderr,"xmax/umax capped at 4.2e9\n"); return 2; }

    gmp_printf("# k=%lld  n in [%Zd, %Zd)  xmax=%llu umax=%llu chunk=%llu time=%.0fs\n",
               (long long)k,n0,n1,(unsigned long long)xmax,(unsigned long long)umax,
               (unsigned long long)chunk,tlimit);
    fflush(stdout);

    /* precompute residue table for all moduli m <= M */
    double tstart=now_sec();
    u64 *idx=malloc((M+2)*sizeof(u64));
    u32 *pool=NULL; u64 poolsz=0, poolcap=0, skipped=0;
    idx[0]=idx[1]=0;
    double denx=0, denu=0;
    for(u64 m=1;m<=M;m++){
        u64 out[MAXR]; int c=froots_modm(k,m,out);
        idx[m]=poolsz;
        if(c==-1){ skipped++; c=0; }
        if(c>0){
            if(poolsz+c>poolcap){ poolcap=poolcap? poolcap*2:1<<20;
                if(poolcap<poolsz+c) poolcap=poolsz+c;
                pool=realloc(pool,poolcap*sizeof(u32)); }
            for(int i=0;i<c;i++) pool[poolsz++]= (u32)out[i];
            if(m<=xmax) denx+=(double)c/m;
            if(m<=umax) denu+=(double)c/m;
        }
        idx[m+1]=poolsz;
    }
    double tbuild=now_sec()-tstart;
    printf("# residue table: %llu classes, built in %.1fs, skipped(cap)=%llu\n",
           (unsigned long long)poolsz,tbuild,(unsigned long long)skipped);
    printf("# candidate density: %.3f (x-branch) + %.3f (u-branch) tests per unit n\n",
           denx,denu);
    fflush(stdout);

    Scratch S;
    mpz_inits(S.nn0,S.t0,S.t1,S.t2,S.t3,S.d1,S.d2,S.d3,S.ta,S.tb,S.hn,S.fresh,
              S.y,S.s,S.w,S.xx,S.N,S.q,S.chk,S.yy,S.tmp,NULL);

    g_deadline=now_sec()+tlimit;
    double t0=now_sec();
    mpz_set(lo,n0);
    while(mpz_cmp(lo,n1)<0 && !g_timeout){
        mpz_add_ui(hi,lo,chunk);
        if(mpz_cmp(hi,n1)>0) mpz_set(hi,n1);
        for(u64 m=1;m<=M && !g_timeout;m++){
            u64 c=idx[m+1]-idx[m];
            for(u64 i=0;i<c && !g_timeout;i++){
                u64 r=pool[idx[m]+i];
                if(m<=xmax) scan_class(m,r,0,lo,hi,k,&S);
                if(g_timeout) break;
                if(m<=umax) scan_class(m,r,1,lo,hi,k,&S);
            }
        }
        if(!g_timeout){
            mpz_set(lo,hi);
            double el=now_sec()-t0;
            gmp_printf("# COMPLETE through n=%Zd | cand=%llu | %.2e cand/s | %llu hits | %.0fs\n",
                       lo,(unsigned long long)g_cand,g_cand/el,
                       (unsigned long long)g_hits,el);
            fflush(stdout);
        }
        if(now_sec()>g_deadline) g_timeout=1;
    }
    double el=now_sec()-t0;
    if(g_timeout)
        gmp_printf("# TIMEOUT: coverage complete only through last '# COMPLETE' line; resume with --n0 %Zd\n",lo);
    gmp_printf("# DONE: verified range [%Zd, %Zd) exhaustively for x<=%llu or u<=%llu; "
               "cand=%llu, rate=%.2e/s, hits=%llu, wall=%.0fs\n",
               n0,lo,(unsigned long long)xmax,(unsigned long long)umax,
               (unsigned long long)g_cand,g_cand/el,(unsigned long long)g_hits,el);
    return 0;
}
