theory Chapter3 imports Main begin

(* Exercise 3.1 *)
type_synonym vname = string
datatype aexp = N int | V vname | Plus aexp aexp

type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
"aval (N a) s = a" |
"aval (V x) s = s x" |
"aval (Plus a b) s = aval a s + aval b s"

fun asimp_const :: "aexp \<Rightarrow> aexp" where
"asimp_const (N a) = N a" |
"asimp_const (V x) = V x" |
"asimp_const (Plus p q) = 
 (case (asimp_const p, asimp_const q) of 
  (N a, N b) \<Rightarrow> N (a+b) |
  (x, y) \<Rightarrow> Plus x y)"

fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"plus (N a) (N b) = N (a+b)" |
"plus p (N i) = (if i = 0 then p else Plus p (N i))" |
"plus (N i) p = (if i = 0 then p else Plus (N i) p)" |
"plus p q = (Plus p q)"

fun asimp :: "aexp \<Rightarrow> aexp" where
"asimp (N a) = N a" |
"asimp (V x) = V x" |
"asimp (Plus p q) = plus (asimp p) (asimp q)"

fun optimal :: "aexp \<Rightarrow> bool" where
"optimal (N a) = True" |
"optimal (V x) = True" |
"optimal (Plus (N i) (N j)) = False" |
"optimal (Plus p q) = ((optimal p) \<and> (optimal q))"

theorem "optimal (asimp_const a) = True"
  apply(induction a)
  apply(auto split:aexp.split)
  done


(* Exercise 3.2 *)

fun collect_consts :: "aexp \<Rightarrow> int" where
"collect_consts (N a) = a" |
"collect_consts (Plus a b) = (collect_consts a) + (collect_consts b)" |
"collect_consts (V x) = 0"

fun collect_vars :: "aexp \<Rightarrow> aexp" where 
"collect_vars (N a) = N 0" |
"collect_vars (Plus a b) = Plus (collect_vars a) (collect_vars b)" |
"collect_vars (V x) = V x"

fun full_asimp :: "aexp \<Rightarrow> aexp" where
"full_asimp a = asimp (Plus (collect_vars a) (N (collect_consts a)))"

lemma "aval a s = collect_consts a + aval (collect_vars a) s"   
  apply(induction a arbitrary: s)
  apply(auto)
  done 

theorem "aval (full_asimp a) s = aval a s" 
  apply(induction a rule:full_asimp.induct)
  apply(auto)
  sorry (* Couldn't figure it out *)


(* Exercise 3.3 *)

fun subst :: "vname \<Rightarrow> aexp \<Rightarrow> aexp \<Rightarrow> aexp" where 
"subst x a (N i) = N i" |
"subst x a (V var) = (if var = x then a else (V var))" |
"subst x a (Plus e1 e2) = Plus (subst x a e1) (subst x a e2)"

lemma [simp]: "aval (subst x a e) s = aval e (s(x := aval a s))"
  apply(induction e arbitrary:s)
  apply(auto)
  done

lemma [simp]: "aval a1 s = aval a2 s \<Longrightarrow> aval (subst x a1 e) s = aval (subst x a2 e) s"
  apply(induction e)
  apply(auto)
  done

(* Exercise 3.4 *)

datatype aexpc = Nc int | Vc vname | Plusc aexpc aexpc | Timesc aexpc aexpc 

fun avalc :: "aexpc \<Rightarrow> state \<Rightarrow> val" where
"avalc (Nc a) s = a" |
"avalc (Vc x) s = s x" |
"avalc (Plusc a b) s = avalc a s + avalc b s" | 
"avalc (Timesc a b) s = avalc a s * avalc b s"

fun asimpc :: "aexpc \<Rightarrow> aexpc" where
"asimpc (Nc a) = Nc a" |
"asimpc (Vc x) = Vc x" |
"asimpc (Plusc p q) = 
  (case (asimpc p, asimpc q) of
    (Nc a, Nc b) \<Rightarrow> Nc (a + b) |
    (a, Nc i) \<Rightarrow> (if i = 0 then a else Plusc a (Nc i)) |
    (Nc i, b) \<Rightarrow> (if i = 0 then b else Plusc (Nc i) b) |
    (a, b) \<Rightarrow> Plusc a b)" | 
"asimpc (Timesc p q) = 
  (case (asimpc p, asimpc q) of
    (Nc a, Nc b) \<Rightarrow> Nc (a * b) |
    (a, Nc i) \<Rightarrow> (if i = 0 then (Nc 0) else if i = 1 then a else Timesc a (Nc i)) |
    (Nc i, b) \<Rightarrow>  (if i = 0 then (Nc 0) else if i = 1 then b else Timesc (Nc i) b) |
    (a, b) \<Rightarrow> Timesc a b)"

value "asimpc (Plusc (Nc 0) (Vc []))"

lemma [simp]: "avalc (Plusc p q) s = avalc p s + avalc q s" 
  apply(induction)
  apply(auto)
  done

lemma [simp]: "avalc (Timesc p q) s = avalc p s * avalc q s" 
  apply(induction)
  apply(auto)
  done

theorem "avalc (asimpc p) s = avalc p s"
  apply (induction p)
  apply(auto split:aexpc.split)
  done

(* Exercise 3.5 *)

datatype aexp2 = N2 int | V2 vname | Plus2 aexp2 aexp2 | Times2 aexp2 aexp2 |  Div2 aexp2 aexp2 | Inc2 vname

fun aval2 :: "aexp2 \<Rightarrow> state \<Rightarrow> (val \<times> state) option" where
"aval2 (N2 a) s = Some (a, s)" |
"aval2 (V2 x) s = Some (s x, s)" |
"aval2 (Plus2 p q) s = 
  (case (aval2 p s, aval2 q s) of
    (None, Some _) \<Rightarrow> None |
    (Some _, None) \<Rightarrow> None |
    (Some a, Some b) \<Rightarrow> Some (fst a + fst b, (\<lambda>x. ((snd a) x) + ((snd b) x) - (s x))))" |
"aval2 (Times2 p q) s = 
  (case (aval2 p s, aval2 q s) of
    (None, Some _) \<Rightarrow> None |
    (Some _, None) \<Rightarrow> None |
    (Some a, Some b) \<Rightarrow> Some (fst a * fst b, (\<lambda>x. ((snd a) x) + ((snd b) x) - (s x))))" |
"aval2 (Inc2 x) s = Some (s x, s(x := 1 + (s x)))" |
"aval2 (Div2 p q) s =
  (case (aval2 p s, aval2 q s) of
    (None, Some _) \<Rightarrow> None |
    (Some _, None) \<Rightarrow> None |
    (Some a, Some b) \<Rightarrow> 
      if (fst b) = 0 then 
        None 
      else
        Some ((fst a div fst b), (\<lambda>x. ((snd a) x) + ((snd b) x) - (s x))))"  

(* Exercise 3.6 *)

datatype lexp = Nl int | Vl vname | Plusl lexp lexp | LET vname lexp lexp

fun lval :: "lexp \<Rightarrow> state \<Rightarrow> int" where
"lval (Nl a) s = a" |
"lval (Vl x) s = s x" |
"lval (Plusl a b) s = (lval a s) + (lval b s)" |
"lval (LET x e1 e2) s = lval e2 (s(x := lval e1 s))"

fun inline :: "lexp \<Rightarrow> aexp" where
"inline (Nl a) = (N a)" |
"inline (Vl x) = (V x)" |
"inline (Plusl a b) = Plus (inline a) (inline b)" |
"inline (LET x e1 e2) = subst x (inline e1) (inline e2)"

theorem "aval (inline e) s = lval e s"
  apply(induction e arbitrary: s)
  apply(auto)
  done

(* Exercise 3.7 *)

datatype bexp = Bc bool | Not bexp | And bexp bexp | Less aexp aexp

fun bval :: "bexp \<Rightarrow> state \<Rightarrow> bool" where
"bval (Bc v) s = v" |
"bval (Not b) s = (\<not> (bval b s))" |
"bval (And a b) s = (bval a s \<and> bval b s)" |
"bval (Less a b) s = (aval a s < aval b s)"

fun less :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
"less (N n) (N m) = Bc (n < m)" |
"less a b = Less a b"

fun "and" :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
"and (Bc True) b = b" |
"and b (Bc True) = b" |
"and (Bc False) b = Bc False" |
"and b (Bc False) = Bc False" |
"and a b = And a b"

fun not :: "bexp \<Rightarrow> bexp" where
"not (Bc True) = Bc False" |
"not (Bc False) = Bc True" |
"not b = Not b"

fun bsimp :: "bexp \<Rightarrow> bexp" where
"bsimp (Bc v) = Bc v" |
"bsimp (Not b) = not(bsimp b)" |
"bsimp (And a b) = and (bsimp a) (bsimp b)" |
"bsimp (Less a b) = less (asimp a) (asimp b)"

fun Le :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
"Le a b = Not (Less b a)"

fun Eq :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
"Eq a b = And (Le a b) (Le b a)"

theorem "bval (Eq a1 a2) s = (aval a1 s = aval a2 s)" 
  apply(auto)
  done

theorem "bval (Le a1 a2) s = (aval a1 s \<le> aval a2 s)" 
  apply(auto)
  done

(* Exercise 3.8 *)

datatype ifexp = Bc2 bool | If ifexp ifexp ifexp | Less2 aexp aexp

fun ifval :: "ifexp \<Rightarrow> state \<Rightarrow> bool" where
"ifval (Bc2 v) s = v" |
"ifval (Less2 a b) s = (aval a s < aval b s)" |
"ifval (If cond a b) s = (if (ifval cond s) then (ifval a s) else (ifval b s))"

fun b2ifexp :: "bexp \<Rightarrow> ifexp" where
"b2ifexp (Bc v) = (Bc2 v)" |
"b2ifexp (Less a b) = (Less2 a b)" |
"b2ifexp (Not a) = (If (b2ifexp a) (Bc2 False) (Bc2 True))" |
"b2ifexp (And a b) = (If (b2ifexp a) (b2ifexp b) (Bc2 False))"

fun or :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
"or a b = Not (And (Not a) (Not b))"

fun if2bexp :: "ifexp \<Rightarrow> bexp" where
"if2bexp (Bc2 v) = (Bc v)" |
"if2bexp (Less2 a b) = (Less a b)" |
"if2bexp (If c p q) =
  (case (if2bexp c, if2bexp p, if2bexp q) of
    (cond, a, b) \<Rightarrow> And (or (not cond) a) (or cond b))"

lemma "ifval ( b2ifexp b ) s = bval b s"
  apply (induction b)
  apply (auto)
done

lemma "bval ( if2bexp i ) s = ifval i s"
  apply (induction i)
  sorry (* :( *)

(* Exercise 3.9 *)

datatype pbexp = VAR vname | NOT pbexp | AND pbexp pbexp | OR pbexp pbexp 

fun pbval :: "pbexp \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> bool" where
"pbval (VAR x) s = s x" |
"pbval (NOT b) s = (\<not> pbval b s)" |
"pbval (AND b1 b2) s = (pbval b1 s \<and> pbval b2 s)" | 
"pbval (OR b1 b2) s = (pbval b1 s \<or> pbval b2 s)"

fun is_nnf :: "pbexp \<Rightarrow> bool" where
"is_nnf (VAR x) = True" |
"is_nnf (NOT (VAR x)) = True" |
"is_nnf (NOT _) = False" | 
"is_nnf (AND a b) = conj (is_nnf a) (is_nnf b)" |
"is_nnf (OR a b) = disj (is_nnf a) (is_nnf b)"

fun nnf :: "pbexp \<Rightarrow> pbexp" where 
"nnf (OR a b) = (OR (nnf a) (nnf b))" |
"nnf (AND a b) = (AND (nnf a) (nnf b))" |
"nnf (NOT (AND a b)) = OR (nnf (NOT a)) (nnf (NOT b))" |
"nnf (NOT (OR a b)) = AND (nnf (NOT a)) (nnf (NOT b))" | 
"nnf (NOT (NOT a)) = nnf a" |
"nnf x = x"

theorem "is_nnf (nnf b)" 
  apply(induction b rule: nnf.induct)
  apply(auto)
  done

theorem "pbval (nnf b) s = pbval b s" 
  apply(induction b rule:nnf.induct)
  apply(auto)
  done

fun no_or :: "pbexp \<Rightarrow> bool" where
"no_or (OR a b) = False" | 
"no_or (AND a b) = conj (no_or a) (no_or b)" |
"no_or x = True"

fun is_dnf :: "pbexp \<Rightarrow> bool" where
"is_dnf (VAR _) = True" |
"is_dnf (NOT (VAR _)) = True" |
"is_dnf (NOT x) = False" |
"is_dnf (OR a b) = ((is_dnf a) \<and> (is_dnf b))" |
"is_dnf (AND a b) = ((no_or a) \<and> (no_or b) \<and> (is_nnf a) \<and> (is_nnf b))"

(* TODO: dnf_of_nnf *) 

(* Exercise 3.10 *)

datatype instr = LOADI val | LOAD vname | ADD

type_synonym stack = "val list"

fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack option" where
"exec1 (LOADI n) _ stk  = Some (n # stk) " |
"exec1 (LOAD x) s stk  = Some (s(x) # stk) " |
"exec1 ADD _ (i # j # stk) = Some ((i + j) # stk)" |
"exec1 ADD _ (x) = None"

fun exec :: "instr list \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack option" where
"exec [] _ stk = Some stk" |
"exec (i#is) s stk =
  (case (exec1 i s stk) of 
    Some res \<Rightarrow> exec is s res |
    None \<Rightarrow> None)"

fun comp :: "aexp \<Rightarrow> instr list" where
"comp (N n) = [LOADI n]" |
"comp (V x) = [LOAD x]" |
"comp (Plus e1 e2) = comp e1 @ comp e2 @ [ADD]"

lemma [simp]: "exec is1 s stk = Some new_stk \<Longrightarrow> exec (is1 @ is2) s stk = exec is2 s new_stk" 
  apply(induction is1 arbitrary:stk)
  apply(auto split:option.split)
  done

theorem exec_comp: "exec (comp a) s stk = Some (aval a s # stk)"
  apply(induction a arbitrary:stk)
  apply(auto)
  done

(* Exercise 3.11 *)

type_synonym reg = "nat"

datatype rinstr = LDI int reg | LD vname reg | ADD reg reg 

fun rexec1 :: "rinstr \<Rightarrow> state \<Rightarrow> (reg \<Rightarrow> int) \<Rightarrow> reg \<Rightarrow> int" where
"rexec1 (LDI i r) s rs = rs(r := i)" |
"rexec1 (LD x r) s rs = rs(r := (s x))" |
"rexec1 (ADD r1 r2) s rs = rs(r1 := (rs r1) + (rs r2))"

fun rexec :: "rinstr list \<Rightarrow> state \<Rightarrow> (reg \<Rightarrow> int) \<Rightarrow> reg \<Rightarrow> int" where
"rexec [] _ rs = rs" |
"rexec (i # is) s rs = rexec is s (rexec1 i s rs)"

fun rcomp :: "aexp \<Rightarrow> reg \<Rightarrow> rinstr list" where
"rcomp (N x) r = [LDI x r]" |
"rcomp (V v) r = [LD v r]" | 
"rcomp (Plus a b) r = rcomp a r @ rcomp b (r+1) @ [ADD r (r + 1)]"

lemma [simp]: "rexec (xs @ ys) s rs = rexec ys s (rexec xs s rs)"
  apply(induction xs arbitrary: rs)
  apply(auto)
  done

lemma [simp]: "r < q \<Longrightarrow> rexec (rcomp a q) s rs r = rs r"
  apply (induction a arbitrary: rs r q)
  apply (auto)
  done

theorem "rexec (rcomp a r) s rs r = aval a s" 
  apply(induction a arbitrary: rs r)
  apply(auto)
  done

(* Exercise 3.12 *)

datatype instr0 = LDI0 val | LD0 vname | MV0 reg | ADD0 reg 

fun exech0 :: "instr0 \<Rightarrow> state \<Rightarrow> (reg \<Rightarrow> int) \<Rightarrow> reg \<Rightarrow> int" where
"exech0 (LDI0 i) s rs = rs(0 := i)" |
"exech0 (LD0 v) s rs = rs(0 := s v)" |
"exech0 (ADD0 r) s rs = rs(0 := (rs 0) + (rs r))" | 
"exech0 (MV0 r) s rs = rs(r := (rs 0))"

fun exec0 :: "instr0 list \<Rightarrow> state \<Rightarrow> (reg \<Rightarrow> int) \<Rightarrow> reg \<Rightarrow> int" where
"exec0 [] _ rs = rs" |
"exec0 (i # is) s rs = exec0 is s (exech0 i s rs)"

fun comp0 :: "aexp \<Rightarrow> reg \<Rightarrow> instr0 list" where
"comp0 (N x) r = [LDI0 x]" |
"comp0 (V v) r = [LD0 v]" | 
"comp0 (Plus a b) r = (comp0 a (r + 1)) @ [MV0 (r + 1)] @ (comp0 b (r + 2)) @ [ADD0 (r + 1)]"

lemma [simp]: "exec0 (xs @ ys) s rs = exec0 ys s (exec0 xs s rs)"
  apply(induction xs arbitrary: rs)
  apply(auto)
  done

lemma [simp]: "0 < r \<and> r < q \<Longrightarrow> exec0 (comp0 a q) s rs r = rs r"
  apply (induction a arbitrary: rs r q)
  apply (auto)
  done

theorem "exec0 (comp0 a r) s rs 0 = aval a s" 
  apply(induction a arbitrary: rs r)
  apply(auto)
  done

end