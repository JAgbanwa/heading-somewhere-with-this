K = 19;
\\ branch 0: x-fiber  E_x: V^2 = U^3+36x^2U^2+432x^4U+1296x^6-1296K x^3,  n=U/(36x)
\\ branch 1: u-fiber  F_u: V^2 = U^3+144u^2U^2+6912u^4U+82944u^6-34944*19... use 663552K? a6=82944u^6-663552*K*u^3, n=U/(288u)
chk(br, m, Q) = {
  my(U = Q[1]);
  if (type(U) != "t_INT" && denominator(U) != 1, return);
  if (br == 0,
    if (U % (36*m) == 0,
      my(n = U/(36*m));
      if (n > 0 && (36*n^3-K) % m == 0,
        my(t = (6*n+m)^2 + (36*n^3-K)/m, y);
        if (issquare(t,&y),
          print(">>> SOLUTION x=",m," n=",n," y=",y," digits(n)=",#digits(n)))))
  ,
    if (U % (288*m) == 0,
      my(n = U/(288*m), s2 = Q[2]);
      if (n > 0 && denominator(s2)==1 && s2 % (288*m^2)==0,
        my(s = abs(s2/(288*m^2)), w = s - m - 12*n);
        if (w > 0 && w % 4 == 0,
          my(x = w/4, y = x+6*n+m);
          if ((36*n^3-K) % x == 0 && y^2 == (6*n+x)^2+(36*n^3-K)/x,
            print(">>> SOLUTION x=",x," n=",n," y=",y," digits(n)=",#digits(n)," via u=",m))))));
}
scan(br, lo, hi, tmo) = {
  for (m = lo, hi,
    if (gcd(m,6) != 1, next);
    my(a2, a4, a6);
    if (br == 0,
      a2=36*m^2; a4=432*m^4; a6=1296*m^6-1296*K*m^3,
      a2=144*m^2; a4=6912*m^4; a6=82944*m^6-663552*K*m^3);
    my(E = ellinit([0,a2,0,a4,a6]), R, tor = elltors(E));
    iferr(R = alarm(tmo, ellrank(E)), err,
          print(if(br==0,"x=","u="), m, "  ellrank TIMEOUT/ERR"); next);
    if (type(R) == "t_ERROR", print(if(br==0,"x=","u="), m,"  TIMEOUT"); next);
    my(pts = R[4], tag = Str(if(br==0,"x=","u="), m));
    print(tag, "  rank[", R[1], ",", R[2], "]  tors=", tor[1], "  gens_found=", #pts);
    \\ enumerate small combinations of generators (+torsion) looking for integral points
    if (#pts > 0,
      my(G = ellsaturation(E, pts, 100));
      
      for (i = 1, #G,
        for (k = 1, 24,
          my(Q = ellmul(E, G[i], k));
          if (Q != [0], chk(br, m, Q));
        ));
      if (#G >= 2,
        for (k1 = -6, 6, for (k2 = 1, 6,
          if (k1 == 0, next);
          my(Q = elladd(E, ellmul(E,G[1],k1), ellmul(E,G[2],k2)));
          if (Q != [0], chk(br, m, Q)))));
    );
  );
}
\\ Usage:  gp -q rank_scan.gp cmd.gp   where cmd.gp contains e.g.:
\\   scan(0, 1, 200, 60);   \\ x-fibers 1..200, 60s ellrank timeout each
\\   scan(1, 1, 200, 60);   \\ u-fibers
\\ Rank-0 fibers with trivial torsion are ELIMINATED for all n.
\\ Rank>=1 fibers with no generator found: run ellheegner(E) (long) or Sage/Magma
\\ integral_points — these large-height fibers are where very large solutions live.
