def teskeMinimizeAtJ(S, B, j, goth_p, N, primesPossiblyDividingGroupOrder):
    '''
    INPUT:
        S - a list of generators of the subgroup
        B - a list of relations (lower triangular), the j-1 first of which are minimal
        j - an integer between 0 and #S-1
        goth_p - the place we are considering
        N - the power of goth_p we are quotienting by
        primesPossiblyDividingGroupOrder - any upper bound for the maximal prime divisor in phi(R) = phi(N).

    OUTPUT:
        B', same as B, except that the j'th relation is replaced by a j'th-minimal one.
    '''

    def findX(k,S,B,j,goth_p, N,x,c,gcdP0Bkk,p0,m):
        if k==-1:
            #check whether the x-vector is a relation:
            K = goth_p.number_field()
            StoX = 1
            for i in range(j+1):
                StoX = StoX * K.coerce(S[i])**x[i]
            return (StoX - 1) >= N

        else:
            if gcdP0Bkk[k]==0:
                print("Some error occured. Parameters k,S,j,R,x,c,gcdP0Bkk:",k,S,j,R,x,c,gcdPoBkk)

            #try all possible values for x[k] and go deeper into the recursion:

            #m = [a for a in range(j)]
            #for i in range(j-1,k,-1):     #i=j-1...k+1
            #    m[i] = B[j][i] - p0*x[i]
            #    for n in range(i+1,j):
            #        m[i] = m[i] - m[n]*B[n][k]    # Important: I think here B[n][k] must be replaced by B[n][i]! (I think Teske's paper has a typo here.)
            #    m[i] = ZZ(m[i] / B[i][i])

            L = B[j][k]
            for i in range(k+1,j):
                L = L - m[i]*B[i][k]

            if not (L in ZZ):
                print("Some error occured. Parameters p0,L,m,k,S,B,j,R,x,c,gcdP0Bkk:",p0,L,m,k,S,B,j,R,x,c,gcdPoBkk)

            if L%gcdP0Bkk[k] != 0:
                return False
            L = ZZ(L / gcdP0Bkk[k]) % B[k][k]
            Rt = ZZ(B[k][k]/gcdP0Bkk[k])

            for rk in range(0,gcdP0Bkk[k]):
                x[k] = (L*c[k] + Rt*rk) % B[k][k]
                if not(x[k].is_integral()):
                    print("Error!")
                m[k] = B[j][k]-p0*x[k]
                for n in range(k+1,j):
                    m[k] = m[k] - m[n]*B[n][k]
                m[k] = ZZ(m[k] / B[k][k])

                if findX(k-1,S,B,j,goth_P,N,x,c,gcdP0Bkk,p0,m):
                    return True

            return False

    #The following takes way too long for large primes in S:
    #P = []        #primes that may reduce b_{jj}
    #for i in prime_range(maxP+1):
    #    if B[j][j]%i == 0:
    #        P.append(i)

    #So let's do it quicker using more knowledge about the underlying group:
    P = [] #primes that may reduce b_{jj}
    for p in primesPossiblyDividingGroupOrder:
        if B[j][j]%p == 0:
            P.append(p)

    #print(S,j,primesPossiblyDividingGroupOrder, P)

    while True:
        #Reduce j'th relation by all previous ones:
        for k in range(j-1,-1,-1):             #k=j-1,...,0
            f = round(B[j][k]/B[k][k])
            if f != 0:
                for i in range(j+1):
                    B[j][i] = B[j][i] - f*B[k][i]

        if len(P) == 0:        #no primes left for reduction
            return B
        p0 = P[0]

        c = [a for a in range(j)]
        for k in range(j):
            c[k] = xgcd(p0,B[k][k])[1]   #a number ck such that gcd(p0,Bkk) = p*ck + Bkk*ak

        gcdP0Bkk = range(j)
        for k in range(j):
            gcdP0Bkk[k] = gcd(p0,B[k][k])

        x = range(j+1)
        x[j] = ZZ(B[j][j]/p0)

        if findX(j-1,S,B,j,goth_P, N,x,c,gcdP0Bkk,p0,[a for a in range(j)]):
            #smaller relation x has been found:
            for i in range(j+1):
                B[j][i] = x[i]
            if x[j]%p0 != 0:
                P.remove(p0)
        else:
            #reducing with respect to p0 is impossible:
            P.remove(p0)

    return B

def teskeMinimize(S, B, goth_P, N, primesPossiblyDividingGroupOrder):
    '''
    INPUT:
        S - a list of generators of a subgroup of R
        B - a list of |S| relations (lower triangular)
        goth_p - the place we are considering
        N - the power of goth_p we are quotienting by
        primesPossiblyDividingGroupOrder - any upper bound for the
            maximal prime divisor in phi(R) = phi(N).

    OUTPUT:
        B', same as B, except that for each j, the j'th relation is
            replaced by a j'th-minimal one.
    '''

    for j in range(len(B)):
        B = teskeMinimizeAtJ(S, B, j, goth_P, N, primesPossiblyDividingGroupOrder)
    return B

#Actually not needed anymore, can use Teske directly instead:
def findMinimalRelations(S,p,n):
    '''
    Input:
        S - list of primes (or arbitrary integers)
        p - a prime (if p in S, then we remove p from S)
        n - an integer

    Output:
        B - a list of minimal relations
    '''

    #print("phi(p^n) =",p^(n-1)*(p-1))

    if S.count(p)>0:
        S.remove(p)
    l = len(S)
    B = [a for a in range(l)]
    for i in range(l):
        B[i] = zero_vector(l).list()
        B[i][i] = exponentOfXmodPtoTheN(S[i],p,n)
    R = IntegerModRing(p^n)
    #print(B[0][0])
    #print(R.coerce(1))

    primesPossiblyDividingGroupOrder = primes_divide(R.unit_group_order())

    return teskeMinimize(S,B,R,primesPossiblyDividingGroupOrder)