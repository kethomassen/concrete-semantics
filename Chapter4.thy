theory Chapter4 imports Main begin

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun set :: "'a tree \<Rightarrow> 'a set" where
"set Tip = {}" |
"set (Node l x r) = (set l) \<union> (set r) \<union> {x}" 

fun ord :: "int tree \<Rightarrow> bool" where
"ord Tip = True" |
"ord (Node l v r) = ((ord l) \<and> (ord r) \<and> (\<forall>e \<in> set l. e \<le> v) \<and> (\<forall>e \<in> set r. v \<le> e))" 

fun ins :: "int \<Rightarrow> int tree \<Rightarrow> int tree" where
"ins val Tip = Node Tip val Tip" |
"ins val (Node l x r) = 
  (if x = val then  
    (Node l x r) 
  else if x > val then
    (Node (ins val l) x r)
  else
    (Node l x (ins val r)))"

lemma[simp]: "set (ins x t) = {x} \<union> set t"
  apply(induction t)
  apply(auto)
  done

theorem "ord t \<Longrightarrow> ord (ins i t)" 
  apply(induction t arbitrary:s)
  apply(auto)
  done

(* Exercise 4.2 *)

inductive palindrome :: "'a list \<Rightarrow> bool" where
"palindrome []" |
"palindrome xs \<Longrightarrow> palindrome (a # xs @ [a])"

lemma "palindrome xs \<Longrightarrow> rev xs = xs"
  apply(induction xs rule:palindrome.induct)
  apply(auto)
  done

(* Exercise 4.3 *)

inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl: "star r x x" |
step: "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

inductive star' :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl': "star' r x x" |
step': "star' r x y \<Longrightarrow> r y z \<Longrightarrow> star' r x z"

lemma [simp]: "star r x y \<Longrightarrow> r y z \<Longrightarrow> star r x z"
  apply(induction rule:star.induct)
  apply(auto intro: refl step)
  done

theorem "star' r x y \<Longrightarrow> star r x y" 
  apply(induction rule:star'.induct)
  apply(auto intro: refl)
  done

lemma [simp]: "star' r y z \<Longrightarrow> r x y \<Longrightarrow> star' r x z"
  apply (induction rule:star'.induct)
  apply (auto intro: refl' step')
  done

theorem "star r x y \<Longrightarrow> star' r x y"
  apply(induction rule:star.induct)
  apply(auto intro: refl')
  done

(* Exercise 4.4 *)


inductive iter :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> int \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"  where
iter_refl: "iter r 0 x x" |
iter_step: "r x y \<Longrightarrow> iter r n y z \<Longrightarrow> iter r (n + 1) x z"

theorem "star r x y \<Longrightarrow> \<exists>n. iter r n x y"
  apply(induction rule:star.induct)
  apply(auto intro: iter_refl iter_step)
  done

(* Exercise 4.5 *)

datatype alpha = alpha | beta

inductive S :: "alpha list \<Rightarrow> bool" where
S_1: "S []" |
S_2: "S w \<Longrightarrow> S (alpha # w @ [beta])" |
S_3: "S w \<Longrightarrow> S x \<Longrightarrow> S (w @ x)"

inductive T :: "alpha list \<Rightarrow> bool" where
T_1: "T []" |
T_2: "T w \<Longrightarrow> T x \<Longrightarrow> T (w @ [alpha] @ x @ [beta])"

theorem T_implies_S: "T w \<Longrightarrow> S w" 
  apply(induction rule:T.induct)
  apply(auto intro:S_1 S_2 S_3)
  done

lemma TT: "T w \<Longrightarrow> T x \<Longrightarrow> T (x @ w)"
  apply(induction rule: T.induct)
  apply(simp)
  apply(metis T.simps append.assoc)
  done

theorem S_implies_T: "S w \<Longrightarrow> T w" 
  apply(induction rule:S.induct)
  apply(auto intro: T_1 T_2)
  apply(metis T.simps T_1 append.left_neutral append_Cons)
  apply(auto intro: TT)
  done

theorem "S w = T w"
  apply(auto intro: T_implies_S S_implies_T)
  done

(* Exercise 4.6 *)

type_synonym vname = string
datatype aexp = N int | V vname | Plus aexp aexp

type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
"aval (N a) s = a" |
"aval (V x) s = s x" |
"aval (Plus a b) s = aval a s + aval b s"

inductive rel_aval :: "aexp \<Rightarrow> state \<Rightarrow> val \<Rightarrow> bool" where
ra_N: "rel_aval (N a) s a" |
ra_V: "rel_aval (V x) s (s x)" |
ra_P: "rel_aval p s px \<Longrightarrow> rel_aval q s qx \<Longrightarrow> rel_aval (Plus p q) s (px + qx)"

theorem RA_A: "rel_aval a s v \<Longrightarrow> aval a s = v"
  apply(induction rule:rel_aval.induct)
  apply(auto)
  done

theorem A_RA: "aval a s = v \<Longrightarrow> rel_aval a s v" 
  apply(induction a arbitrary: v)
  apply(auto intro: ra_N ra_V ra_P)
  done

theorem "(aval a s = v) = rel_aval a s v"
  apply(auto intro: RA_A A_RA)
  done

(* Exercise 4.7 *)

datatype instr = LOADI val | LOAD vname | ADD

type_synonym stack = "val list"

abbreviation hd2 where 
"hd2 xs \<equiv> hd (tl xs)"

abbreviation tl2 where 
"tl2 xs \<equiv> tl (tl xs)"

fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack" where
"exec1 (LOADI n) _ stk = (n # stk)" |
"exec1 (LOAD x) s stk = (s(x) # stk)" |
"exec1 ADD _ stk = (hd2 stk + hd stk) # tl2 stk"

fun exec :: "instr list \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack" where
"exec [] _ stk = stk" |
"exec (i#is) s stk = exec is s (exec1 i s stk)"

fun comp :: "aexp \<Rightarrow> instr list" where
"comp (N n) = [LOADI n]" |
"comp (V x) = [LOAD x]" |
"comp (Plus e1 e2) = comp e1 @ comp e2 @ [ADD]"

inductive ok :: "nat \<Rightarrow> instr list \<Rightarrow> nat \<Rightarrow> bool" where
ok_1: "ok n [] n" |
ok_2: "ok n ((LOADI _) # xs) n' \<Longrightarrow> ok (n + 1) xs n'" |
ok_3: "ok n ((LOAD _) # xs) n' \<Longrightarrow> ok (n + 1) xs n'" |
ok_4: "ok n ((ADD) # xs) n' \<Longrightarrow> ok (n - 1) xs n'"

theorem "\<lbrakk> ok n is n'; length stk = n \<rbrakk> \<Longrightarrow> (length (exec is s stk) = n')"
  apply(induction arbitrary: stk rule: ok.induct)
  apply(auto intro: ok_1 ok_2 ok_3 ok_4)
  sorry
  
end