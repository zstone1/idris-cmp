import Data.Fin

data Parity : Nat -> Type where
    Even : {n : Nat} -> Parity (n + n)
    Odd  : {n : Nat} -> Parity (S (n + n))

parity : (n:Nat) -> Parity n
parity Z     = Even {n=Z}
parity (S Z) = Odd {n=Z}
parity (S (S k)) with (parity k)
    parity (S (S (j + j)))     | Even ?= Even {n=S j}
    parity (S (S (S (j + j)))) | Odd  ?= Odd {n=S j}


parity_lemma_2 = proof {
    intro;
    intro;
    rewrite sym (plusSuccRightSucc j j);
    trivial;
}

parity_lemma_1 = proof {
    intro j;
    intro;
    rewrite sym (plusSuccRightSucc j j);
    trivial;
}


satisfyRoot2 : Pair Nat Nat -> Type
satisfyRoot2 (p, q) = p*p = 2*q*q

divides : (x : Nat) -> (y:Nat) -> Type
divides x y = (k:Nat** ( x * k = y))

reduced : Pair Nat Nat -> Type
reduced (p, q) = (gcd p q) = S Z
 
distMultPair : (f:Nat -> Nat) -> (x:Nat) -> (y :Nat) -> Type
distMultPair f x y =  (f (x*y) = f(x) * f(y))

distMult : (Nat -> Nat) -> Type
distMult f = (x:Nat) -> (y :Nat) -> distMultPair f x y

rewriteDist : (f:Nat -> Nat) -> distMultPair f p q -> (p*q = r) -> f(p)*f(q) = f(r)
rewriteDist f dist eq = rewrite sym dist in cong eq

nDividesfA : (f: Nat -> Nat) -> distMult f -> divides x y -> divides (f x) (f y)
nDividesfA {x = x} fn fDist (k ** xkEQy) = (fn k ** rewriteDist fn (fDist x k) xkEQy)

total
unitProd : {x:Nat} -> {y:Nat} -> x*y = 1 -> (x = 1, y = 1)
unitProd {x = Z} eq = void $ SIsNotZ (sym eq)
unitProd {x = x'} {y = Z} eq = void $ SIsNotZ $ rewrite multCommutative Z x' in sym eq
unitProd {x = S Z} {y = S Z} eq = (Refl, Refl)
unitProd {x = S(x')} {y = S( S y')} eq = 
	let preds = cong {f = Prelude.Nat.pred} eq in
	void $ SIsNotZ preds
unitProd {x = S(S(x'))} {y = (S Z)} eq = 
	let preds = cong {f = Prelude.Nat.pred} eq in
	void $ SIsNotZ preds


intDomain : a*b = 0 -> Either (a=Z) (b=Z)
intDomain {a=Z} eq =Left eq
intDomain {b=Z} eq = Right Refl
intDomain {a=S(x)} {b=S(y)} eq = void $ SIsNotZ eq


minusPlusSelf : ((minus a b) + b) = a 
minusPlusSelf {a=a} {b=Z} =rewrite  minusZeroRight a in plusZeroRightNeutral a
--minusPlusSelf {a=Z} {b=b} =Refl
--minusPlusSelf {a=a} {b=(S k)} = 
--	let e1 = plusSuccRightSucc b


multInjective : {a,b,c:Nat} -> Not (a=Z) -> a*b = a*c -> b = c 
multInjective {a = a} {b = b} {c=c} aNotZ eq = 
	let e1 : (minus (a*b) (a*c) = minus (a*c) (a*c)) = cong {f = (\e => minus e (a*c))} eq in 
	let e2 : (minus (a*b) (a*c) = Z) = rewrite minusZeroN (a*c) in e1 in 
	let e3 : (a*(minus b c) = Z) = rewrite multDistributesOverMinusRight a b c in e2 in
	let e4 : (minus b c = Z) =
		(case intDomain {a=a} {b = minus b c} e3 of 
			Left aEQz => void $ (aNotZ aEQz)
			Right realCase => realCase) in 
	let e5 : ((minus b c) + c = c) = cong {f = (\e => e+c)} e4 in 
	let e6 : (b = c) = rewrite sym $ minusPlusSelf {a = b}{b=c} in e5 in
	e6

total
helperC: minus (x*a)  (x*b) = (S Z)  -> x*(minus a b) = (S Z)
helperC {x = x} {a=a} {b=b} eq = rewrite multDistributesOverMinusRight x a b in eq 
	
total
successorCoPrime : (divides k x) -> divides k (S x) -> k = (S Z)
successorCoPrime (p ** xEQ) (q ** sxEQ) = 
	let e1 : (k*q               = S(k*p))				 = rewrite xEQ in sxEQ in 										
	let e2 : (minus (k*q) (k*p) = minus (S(k*p)) (k*p))  = cong {f = \e => minus e (k*p)} e1 in 			
	let e3 : (minus (k*q) (k*p) = (S Z))				 = rewrite minusOneSuccN (k*p) in e2 in				 						
	let e4 : (k*(minus q p)     = (S Z))				 = rewrite multDistributesOverMinusRight k q p in e3 in						
	let (e5,_) : (k = (S Z), _) = unitProd (e4) in
	e5
	
	

xPlusxEq2x : {x:Nat} ->  2*x = x + x 
xPlusxEq2x  {x = x} = rewrite plusZeroRightNeutral x in Refl


helperD : (j:Nat) -> (n:Nat ** 2*n = S(S(j+j) * S(j+j)))
helperD j = ?arithmetic_hole

twoDividesPower : divides 2 (n*n) -> divides 2 n
twoDividesPower {n = n} div with (parity n)
	twoDividesPower {n = j+j} div | Even = (j ** rewrite sym $ xPlusxEq2x {x = j} in Refl)
	twoDividesPower {n = S(j+j)} div | Odd =  
		let nnSuccIsEven = helperD j in 
		let twoEqOne = successorCoPrime {k = 2} div nnSuccIsEven in 
		void $ SIsNotZ $ cong { f= Prelude.Nat.pred} twoEqOne


		
root2Half : p*p = 2 *(q*q) -> divides 2 p
root2Half{p = p}{q=q} eq = 
	let a = (q*q ** sym eq) in
	let (k ** twoDivP) = twoDividesPower a in 
	?foo
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		


