# Main L value computation function
#Code to compute the |L(f,chi,s)|^2

# -----------------------------------------------------------------------------------------------------------------
# This section is for character functions for the non-degenerate case 

def char_func(n,a): #Returns the power k such that gen^k congruent to a mod n
    Gp = Zmod(n)
    A = Gp.unit_group()
    gen = A.gens_values()[0]
    k=1
    Alist = list(A)
    AlistA = list(prod((a^b for a, b in zip(A.gens(), g.list())), A.one()) for g in A)
    AlistZn = [h.value() for h in AlistA]
    if a in AlistZn:
        while mod(gen^k,n) != a:
            k+=1
        return k
    else:
        return "Error, input was not a value in Z/nZ cross"

def rat_mod_int(a, k):# rational modulo an integer
    return a.numerator() % (k * a.denominator()) / a.denominator()
    
def primitive_character_7(input_number):
    img_of_generator = (2/3) # As in, the generator maps to e^((4*pi*i)/3)
    modulus = 7
    k = char_func(modulus,input_number)
    Mnum = rat_mod_int((2*img_of_generator*k), 2)
    return exp(Mnum*pi*I)

    # We know that chi of the generator maps to img_of_generator, and thus chi(gen) = img_of_generator
    # Then if we want chi(N), and we know N = gen^k, we can do chi(N) = chi(gen^k) = chi(gen)^k = img_of_generator^k
    # We know k from the char_func function
    
def primitive_character_9(input_number):
    img_of_generator = (1/3) # As in, the generator maps to e^((2*pi*i)/3)
    modulus = 9
    k = char_func(modulus,input_number)
    Mnum = rat_mod_int(2*img_of_generator*k,2)
    return exp(Mnum*pi*I)

def prim_character(modulus, value):
    selected_character = None
    if modulus == 7:
        selected_character = primitive_character_7
    elif modulus == 9:
        selected_character = primitive_character_9
    else:
        print("Invalid choice of character, made a mistake entering modulus")
    
    if selected_character:
        return selected_character(value)

# --------------------------------------------------------------------------------------------------------
def Gauss_sum(character_modulus): #Didn't end up using this
    S=0
    for j in range(1,character_modulus):
        if gcd(j,character_modulus) == 1:
            S += prim_character(character_modulus,j) * e^((2*pi*I*j)/character_modulus)
    return S

# ---------------------------------------------------------------------------------------------------------
#Main Function
def Lvalue_abs_squared(f_weight,character_modulus,K):
    
    # GL2Action of a matrix on an arbitrary polynomial
    def GL2Act(M1,P):
        x,y = var('x,y')
        a = M1[0]; b = M1[1]; c = M1[2]; d = M1[3];
        z1 = a*x + c*y
        z2 = b*x + d*y
        g = P.subs({x: z1, y: z2})
        f = expand(g)
        return f
    
    #Manins Trick
    def ManinsTrick(a,m):
        # Make the continued fraction
        cfrac = continued_fraction(a/m)
        cverg = cfrac.convergents()
        
        # Append convergents to a list
        BigList = []
        for i in [0..len(cverg)-1]:
            L = []
            if cverg[i] == 0: 
                L.append(0)
                L.append(1)
            else:
                L.append(cverg[i].numerator())
                L.append(cverg[i].denominator())
            BigList.append(L)
        
        Full_convergents = []
        Negative_convergents = []
        b_a_negative1 = [1,0]
        b_a_negative2 = [0,1]
        Negative_convergents.append(b_a_negative2)
        Negative_convergents.append(b_a_negative1)

        Full_convergents += Negative_convergents
        Full_convergents += BigList
        
        # Turn convergents into matrices
        Matrices_list = []
        for i in [0..len(Full_convergents)-2]:
            k = i-1
            sign = (-1)^(k-1)
            g_k = matrix([
                [Full_convergents[i+1][0], Full_convergents[i][0]*sign],
                [Full_convergents[i+1][1], Full_convergents[i][1]*sign]
            ])
            Matrices_list.append(g_k)
        
        # Flatten the matrices back into lists
        Flat_Matrices = []
        for Matrix in Matrices_list:
            Lst = []
            Lst.append(Matrix[0,0])
            Lst.append(Matrix[0,1])
            Lst.append(Matrix[1,0])
            Lst.append(Matrix[1,1])
            Flat_Matrices.append(Lst)
    
        #Polynomials
        x, y = var('x,y')
        P12(x,y) = (4*x^9*y^1 - 25*x^7*y^3 + 42*x^5*y^5 - 25*x^3*y^7 + 4*x^1*y^9) 
        P18(x,y) = 24000/43867*x^16 - 32/3*x^14*y^2 + 100/3*x^12*y^4 - 104/3*x^10*y^6 + 104/3*x^6*y^10 - 100/3*x^4*y^12 + 32/3*x^2*y^14 - 24000/43867*y^16
        P22(x,y) = -114000/77683*x^20 + 608/21*x^18*y^2 - 95*x^16*y^4 + 2584/21*x^14*y^6 - 1615/21*x^12*y^8 + 1615/21*x^8*y^12 - 2584/21*x^6*y^14 + 95*x^4*y^16 - 608/21*x^2*y^18 + 114000/77683*y^20
        
        if f_weight == 12:
            P(x,y) = P12
        if f_weight == 18:
            P(x,y) = P18
        if f_weight == 22:
            P(x,y) = P22
        
        Sum_poly = 0
        for mlist in Flat_Matrices:
            Acted_poly = GL2Act(mlist,P)
            Sum_poly += Acted_poly
    
        Final_Poly = (-1)*Sum_poly + P
    
        return(Final_Poly)

    # Index m, the point of symmetry, and create the required Dirichlet Character
    m = K-1
    l = f_weight
    
    def LeftSide(character_modulus): 
        G = Zmod(character_modulus)
        Glist = G.list_of_elements_of_multiplicative_group()
        Sum_polynomial = 0
        for j in Glist:
            Q0 = ManinsTrick(j,character_modulus)
            M0 = [1, -j/character_modulus, 0, 1]
            R0 = GL2Act(M0,Q0)
            Sum_polynomial += (prim_character(character_modulus,j)) * R0
        return Sum_polynomial
    
    # Compute the entire left hand side of the formula
    Poly = LeftSide(character_modulus)
    
    # Pull out the coefficient for the point of symmetry
    x,y  = var('x', 'y')
    CoeffX5 = Poly.coefficient(x^m*y^m)
    
    # Now we can take the absolute value squared, and then divide by the square of the absolute value of the Gauss_sum, which we know to be the character modulus

    LVAL = (abs(CoeffX5))^2 / character_modulus
    
    return LVAL




#Main Function for the Case where K is a Cubic field of the form Q x Q(sqrt{D}) (Degenerate Quadratic Case)

def LvalueQuadraticCase(f_weight,character_modulus,K):
    # Note that character_modulus = D_K the discriminant of the number field
    
    chi = kronecker_character(character_modulus)
    
    # GL2Action of a matrix on an arbitrary polynomial
    def GL2ActQuadratic(M1,P):
        x,y = var('x,y')
        a = M1[0]; b = M1[1]; c = M1[2]; d = M1[3];
        z1 = a*x + c*y
        z2 = b*x + d*y
        g = P.subs({x: z1, y: z2})
        f = expand(g)
        return f
    
    #Manins Trick
    def ManinsTrickQuadratic(a,m):
        # Make the continued fraction
        cfrac = continued_fraction(a/m)
        cverg = cfrac.convergents()
        
        # Append convergents to a list
        BigList = []
        for i in [0..len(cverg)-1]:
            L = []
            if cverg[i] == 0: 
                L.append(0)
                L.append(1)
            else:
                L.append(cverg[i].numerator())
                L.append(cverg[i].denominator())
            BigList.append(L)
        
        Full_convergents = []
        Negative_convergents = []
        b_a_negative1 = [1,0]
        b_a_negative2 = [0,1]
        Negative_convergents.append(b_a_negative2)
        Negative_convergents.append(b_a_negative1)

        Full_convergents += Negative_convergents
        Full_convergents += BigList
        
        # Turn convergents into matrices
        Matrices_list = []
        for i in [0..len(Full_convergents)-2]:
            k = i-1
            sign = (-1)^(k-1)
            g_k = matrix([
                [Full_convergents[i+1][0], Full_convergents[i][0]*sign],
                [Full_convergents[i+1][1], Full_convergents[i][1]*sign]
            ])
            Matrices_list.append(g_k)
        
        # Flatten the matrices back into lists
        Flat_Matrices = []
        for Matrix in Matrices_list:
            Lst = []
            Lst.append(Matrix[0,0])
            Lst.append(Matrix[0,1])
            Lst.append(Matrix[1,0])
            Lst.append(Matrix[1,1])
            Flat_Matrices.append(Lst)
    
        #Polynomials
        x, y = var('x,y')
        P12(x,y) = (4*x^9*y^1 - 25*x^7*y^3 + 42*x^5*y^5 - 25*x^3*y^7 + 4*x^1*y^9) 
        P18(x,y) = 24000/43867*x^16 - 32/3*x^14*y^2 + 100/3*x^12*y^4 - 104/3*x^10*y^6 + 104/3*x^6*y^10 - 100/3*x^4*y^12 + 32/3*x^2*y^14 - 24000/43867*y^16
        P22(x,y) = -114000/77683*x^20 + 608/21*x^18*y^2 - 95*x^16*y^4 + 2584/21*x^14*y^6 - 1615/21*x^12*y^8 + 1615/21*x^8*y^12 - 2584/21*x^6*y^14 + 95*x^4*y^16 - 608/21*x^2*y^18 + 114000/77683*y^20
        
        if f_weight == 12:
            P(x,y) = P12
        if f_weight == 18:
            P(x,y) = P18
        if f_weight == 22:
            P(x,y) = P22
        
        Sum_poly = 0
        for mlist in Flat_Matrices:
            Acted_poly = GL2ActQuadratic(mlist,P)
            Sum_poly += Acted_poly
    
        Final_Poly = (-1)*Sum_poly + P
    
        return(Final_Poly)

    # Index m, the point of symmetry, and create the required Dirichlet Character
    m = K-1
    l = f_weight
    
    def LeftSideQuadratic(character_modulus):  # NEED TO CHANGE THIS
        G = Zmod(character_modulus)
        Glist = G.list_of_elements_of_multiplicative_group()
        Sum_polynomial = 0
        for j in Glist:
            Q0 = ManinsTrickQuadratic(j,character_modulus)
            M0 = [1, -j/character_modulus, 0, 1]
            R0 = GL2ActQuadratic(M0,Q0)
            Sum_polynomial += (chi(j)) * R0
        return Sum_polynomial
    
    # Compute the entire left hand side of the formula
    Poly = LeftSideQuadratic(character_modulus)
    
    # Pull out the coefficient for the point of symmetry
    x,y  = var('x', 'y')
    CoeffX5 = Poly.coefficient(x^m*y^m)
    
    # Now we can take the absolute value squared, and then divide by the absolute value of the Gauss_sum, which we know to be the character modulus

    LVAL = (abs(CoeffX5))/(sqrt(character_modulus))
    
    return LVAL


# Code to generate the Binary Cubic Forms

def subgroups(n):
    L1 = []
    Zn = Zmod(n)
    G = Zn.unit_group()
    Glist = list(G)
    GlistG = list(prod((a^b for a, b in zip(G.gens(), g.list())), G.one()) for g in G)
    GlistZn = [h.value() for h in GlistG]
    for j in GlistZn:
        L = []
        k = 1
        while mod(j^k,n) != 1:
            L.append(mod(j^k,n))
            k += 1
        L.append(1)
        L1.append(L)
    return L1



def Find_N(n): #Function to determine which numbers have phi(n) congruent to 0 mod 3
    F = []
    for k in [1..n]:
        if mod(euler_phi(k),3) == 0:
            F.append(k)
    return F
    

def CompN(n): #Finds only the composite N with phi(N) congruent to 0 mod 3
    F = Find_N(n)
    for j in F:
        if j.is_prime():
            F.remove(j)
    return F

E = []
for k in CompN(50): #Finding the composite N such that N generates a cyclic subgroup of size phi(n)/3
    K = subgroups(k)
    for e in K:
        if len(e) == euler_phi(k):
            if k not in E:
                E.append(k)

def ZnCyclic(n): #Function to check if Z/nZ cross is cyclic for n. Recall that Z/nZ is cylic iff n = 2,4 p^k, 2p^k for odd prime p
    if n == 2: 
        return true
    elif n == 4:
        return true
    elif n.is_prime():
        return true
    else: 
        F = factor(n)
        G = list(F)
        if len(G) > 2: #if the prime factorization contains 3 distinct base primes it cannot be of one of our desired forms
            return false
        if len(G) == 2: #This is the case where we need to check if there is a power of 2, and then if that power is one
            if G[0][0] == 2: #Good case #of the form 2^j p^k, need to check j == 1
                if G[0][0] == 1: #Good case, of the form 2^1 p^k
                    return true
                elif G[0][1] != 1: #Bad case, this is of the form 2^j p^k where j > 1
                    return false
            elif G[0][0]!= 2: #Bad Case, product of two primes where both not 2
                return false
        if len(G) == 1: #singular prime to a power, p^k 
            return true

def noncyclics(N): #obtaining a list of n such that Z/nZ cross is cyclic
    nocyc = []
    for i in [2..N]:
        if ZnCyclic(i) is false:
            nocyc.append(i)
    return nocyc

def noncyclicwsubgp(M):
    vals = []
    nocyc = noncyclics(M)
    for i in nocyc:
        if mod(euler_phi(i), 3) == 0:
            vals.append((i))       
    return vals


def valid_n_list(N): #finds all integers n, up to N, such that either (Z/nZ)^* is cyclic, or has a subgroup of size==0(mod 3)
    valid_list = []
    for i in [2..N]:
        if (i in noncyclicwsubgp(N)) is true:
            valid_list.append(i)
        if ZnCyclic(i) is true:
            if mod(euler_phi(i),3) == 0:
                valid_list.append(i)
    return valid_list
    
def order3_fixedfield_cyclotomic_n(n): #gives the fixed field of order 3 of a cyclotomic field of zeta_n
    e = euler_phi(n)/3
    F = CyclotomicField(n)
    z = CyclotomicField(n).gen(); z
    G = F.galois_group(); G 
    for H in G.subgroups():
        if H.order()==e:
            kfixed, embed = H.fixed_field()
    return kfixed

def integer_ring(kfixed): #returns the ring of integers of a given fixed field
    p = kfixed.defining_polynomial()
    z = kfixed.primitive_element()
    OK = kfixed.ring_of_integers()
    return OK

def OK_basis(OK): #gives the basis of ring of integers
    r = OK.gens(); r
    return r

def cubic_poly_of_cyclotomic_n(n): #computes the "good basis" and gives the coefficients of the binary cubic form of the cyclotomic field of zeta_n
    kfixed = order3_fixedfield_cyclotomic_n(n)
    OK = integer_ring(kfixed)
    r = OK_basis(OK)

    #original basis
    B = list(r)
    b1 = B[1]
    b2 = B[2]
    x = b1*b2

    #solving for good basis
    v = [(B[i]*x).trace() for i in range(3)]
    print((B[0]*x).trace())
    M = kfixed.trace_pairing(B); M
    V = vector(v)

    A = M.solve_right(V)

    #new 'good basis' 
    alpha = b1 - A[2]
    beta = b2 - A[1]
    gb = [1,alpha,beta]
    M2 = kfixed.trace_pairing(gb); M2

    # n = alpha*beta, where n is an integer 
    n = alpha*beta

    # m, b, a
    alpha2 = alpha^2
    v2 = [(gb[i]*alpha2).trace() for i in range(3)]
    V2 = vector(v2)
    A2 = M2.solve_right(V2)
    m = A2[0]
    b = A2[1]
    a = -A2[2]

    #l, d, c
    beta2 = beta^2
    v3 = [(gb[i]*beta2).trace() for i in range(3)]
    V3 = vector(v3)
    A3 = M2.solve_right(V3)
    l = A3[0]
    d = A3[1]
    c = -A3[2]

    PXY = [a,b,c,d]
    return PXY

#Code to compute binary cubic forms with the second coefficient in {0,1}

def cubic_coeff_list(n): #takes all values in valid_n_list and outputs the coeff of all the binary cubic forms
    cubic_coeff = []
    l = valid_n_list(n)
    for i in l:
        L = cubic_poly_of_cyclotomic_n(i)
        cubic_coeff.append([i,L])
    return cubic_coeff

def n_value(M):
    a = M[0]
    b = M[1]
    c = M[2]
    d = M[3]
    value = b^2 - 2*c*a
    return value

def disc_f(List):
    a = List[0]
    b = List[1]
    c = List[2]
    d = List[3]
    disc = b^2*c^2 + 18*a*b*c*d - 4*a*c^3 - 4*d*b^3 - 27*a^2*d^2

    return disc

def cubic_coeff_list2(n): #takes all values in valid_n_list and outputs the coeff of all the binary cubic forms
    cubic_coeff = []
    l = valid_n_list(n)
    for i in l:
        L = cubic_poly_of_cyclotomic_n(i)
        cubic_coeff.append(L)
    return cubic_coeff

def GL2_translate(L):
    P = []
    M = []
    if L[0] > 0:
        P.append(L[0])
        P.append(L[1])
        P.append(L[2])
        P.append(L[3])
    else: 
        P.append(-1*L[0])
        P.append(-1*L[1])
        P.append(-1*L[2])
        P.append(-1*L[3])
    if P[1] == 0 or P[1] == 1:
        u = 0
    else:
        if P[1] < 0:
            P[1] = -1*P[1]
            P[3] = -1*P[3]
        if P[1] == 2:
            u = -1*ceil(P[1]/3)
        else:
            u = -1*floor(P[1]/3)
    M.append(P[0])
    M.append(3*P[0]*u + P[1])
    M.append(3*P[0]*u^2 + 2*P[1]*u + P[2])
    M.append(P[0]*u^3 + P[1]*u^2 + P[2]*u + P[3])
    if M[1] < 0:
        M[1] = -1*M[1]
        M[3] = -1*M[3]
    return M

def GL2_translate_list(Q):
    T = []
    n = len(Q)
    for i in [0..n-1]:
        N = GL2_translate(Q[i][1])
        D = n_value(N)
        T.append((Q[i][0],D,N))
    return T

def succinct_list(M):
    L = []
    l = len(M)
    for i in [0..l-1]:
        if M[i][2] not in L:
            L.append(tuple(M[i][2]))
    return L
    
def initialize_dictionary(M):
    coeff_dict={}
    l = len(M)
    for i in [0..l-1]:
        coeff_dict.update({M[i]:zero_vector(ZZ,1)})
    return coeff_dict 



def MonicForms(N):
    Q = cubic_coeff_list(N)
    L = list(Q)
    n = len(L)
    MonicLst = []
    for i in [0..n-1]:
        N = GL2_translate(Q[i][1])
        MonicLst.append((Q[i][0],N))
    return MonicLst  

#Code to compute polynomial for weights 12, 16, 18, and 22

def polynomial(k):
    T,x,y,q = var('T,x,y,q')
    P = 0 
    for i in [2..k]:
        if is_even(i) == True:
            P += ((x^i+1)*(y^i+1)-((x*y)-1)^i-(x+y)^i)*((-bernoulli(i)/(2*i))+q)*((T^i)/factorial(i))
        else:
            P += 0
    Poly = 2*P
    f = exp(Poly)
    S = taylor(f,T,0,k)
    Q = (((x*y)-1)*(x+y))/((x^2)*(y^2)*(T^2))*S
    Cpoly = Q.expand()
    P_mX = 0
    for i in [-1..k-1]:
        if is_odd(i) == True:
            P_mX += (bernoulli(i+1)/factorial(i+1))*(bernoulli(k-i-1)/factorial(k-i-1))*x^i
        else:
            P_mX += 0
    P_mY = 0
    for i in [-1..k-1]:
        if is_odd(i) == True:
            P_mY += (bernoulli(i+1)/factorial(i+1))*(bernoulli(k-i-1)/factorial(k-i-1))*y^i
        else:
            P_mY += 0
    R = (((x^(k-2))-1)*(P_mY)) + ((P_mX)*((y^(k-2))-1))
    Ck = (-(factorial(k-2)) + (2*k*factorial(k-2)*q/bernoulli(k)))*R
    F = Cpoly -(((x*y)-1)*(x+y))/((x^2)*(y^2)*(T^2))
    H = F.derivative(T,k-2).expand()
    K = (H - (Ck))
    J = K.subs(T=0).expand()
    L = J.expand().derivative(q,1).subs(q=0)/2
    M = L.polynomial(QQ)
    term_list = list(M.dict().items())
    terms = [c * x^a * y^b for (a, b), c in M.dict().items()]
    Even_powers = []
    for item in terms:
        n = item.degree(x)
        deg_int = ZZ(n)
        if is_even(deg_int) == True: 
            Even_powers.append(item)
            
    Polynomial = sum(Even_powers)


    if is_odd(k/2) == False:
        T = (y*(y^2-1)^2*(y^2-4)*(4*y^2-1))
        S = Polynomial/T
        N = S.polynomial(QQ)
        F = N.factor()
        factors_with_y = []

        for factor, exponent in F:
            if y in factor.variables():
                factors_with_y.append(factor^exponent)
        Z = sum(factors_with_y)
        if Z == 0: 
            M = F
        else: 
            M = F/Z

    else:
        T = (y*(y^2-1)^2*(y^2-4)*(4*y^2-1)*(y^2+1))
        S = Polynomial/T
        N = S.polynomial(QQ)
        F = N.factor()
        factors_with_y = []

        for factor, exponent in F:
            if y in factor.variables():
                factors_with_y.append(factor^exponent)
        Z = sum(factors_with_y)
        if Z == 0: 
            M = F
        else: 
            M = F/Z
    X = M.expand()
    Y = T.expand()
            
    return (X,Y)


