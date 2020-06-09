theory Chapter2 imports Main begin

(* Exercise 2.1 *)

value "1 + (2::nat)"
value "1 + (2::int)"
value "1 - (2::nat)"
value "1 - (2::int)"

(* Exercise 2.2 *)

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 n = n" |
"add (Suc n) m = Suc(add n m)"

theorem AddAssociative: "add (add n m) p = add n (add m p)"
  apply(induction n)
  apply(auto)
  done

lemma [simp]: "add n 0 = n"
  apply(induction n)
  apply(auto)
  done

lemma [simp]: "Suc (add m n) = add m (Suc n)"
  apply(induction m)
  apply(auto)
  done

theorem AddCommutative[simp]: "add n m = add m n"
  apply(induction n)
  apply(auto)
  done

(* Exercise 2.3 *)

fun count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
"count a [] = 0" |
"count a (x # xs) = add (if a = x then 1::nat else 0::nat) (count a xs)"

theorem CountLessThanEqLength: "count x xs \<le> length xs" 
  apply(induction xs)
  apply(auto)
  done

(* Exercise 2.4 *)

fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"snoc [] a = [a]" |
"snoc (x # xs) a = x # (snoc xs a)"

fun reverse :: "'a list \<Rightarrow> 'a list" where 
"reverse [] = []" |
"reverse (x # xs) = snoc (reverse xs) x"

lemma [simp]: "reverse (snoc xs a) = a # reverse xs"
  apply(induction xs)
  apply(auto)
  done

theorem DoubleReverse[simp]: "reverse (reverse xs) = xs"
  apply(induction xs)
  apply(auto)
  done

(* Exercise 2.5 *)
fun sum_upto :: "nat \<Rightarrow> nat" where
"sum_upto 0 = 0" |
"sum_upto n  = (+) n (sum_upto (n - 1))"

theorem "sum_upto n = (n * (n + 1)) div 2"
  apply(induction n)
  apply(auto)
  done

(* Exercise 2.6 *)
datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

(* inorder traversal *)
fun contents :: "'a tree \<Rightarrow> 'a list" where
"contents Tip = []" |
"contents (Node left x right) = contents(left) @ [x] @ contents(right)"

fun sum_tree :: "nat tree \<Rightarrow> nat" where
"sum_tree Tip = 0" |
"sum_tree (Node left x right) = x + (sum_tree left) + (sum_tree right)"

theorem "sum_tree t = sum_list (contents t)" 
  apply(induction t)
  apply(auto)
  done

(* Exercise 2.7 *)
datatype 'a tree2 = Tip 'a | Node "'a tree2" 'a "'a tree2"

fun mirror :: "'a tree2 \<Rightarrow> 'a tree2" where
"mirror (Tip x) = Tip x" | 
"mirror (Node left x right) = Node (mirror right) x (mirror left)"

fun pre_order :: "'a tree2 \<Rightarrow> 'a list" where
"pre_order (Tip x) = [x]" |
"pre_order (Node left x right) = x # (pre_order left @ pre_order right)"

fun post_order :: "'a tree2 \<Rightarrow> 'a list" where
"post_order (Tip x) = [x]" |
"post_order (Node left x right) = (post_order left @ post_order right) @ [x]"

theorem "pre_order (mirror t) = rev (post_order t)"
  apply(induction t)
  apply(auto)
  done

(* Exercise 2.8 *)

fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"intersperse a [] = [a]" | 
"intersperse a (x # xs) = x # a # intersperse a xs"

theorem "map f (intersperse a xs) = intersperse (f a) (map f xs)" 
  apply(induction xs)
  apply(auto)
  done

(* Exercise 2.9 *)

fun itadd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"itadd acc 0 = acc" |
"itadd acc (Suc m) = itadd (Suc acc) m" 

theorem "itadd m n = m + n" 
  apply(induction n arbitrary: m)
  apply(auto)
  done

(* Exercise 2.10 *)
datatype tree0 = Leaf | Node tree0 tree0

fun nodes :: "tree0 \<Rightarrow> nat" where
"nodes Leaf = 1" |
"nodes (Node l r) = 1 + nodes l + nodes r"

fun explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where 
"explode 0 t = t" |
"explode (Suc n) t = explode n (Node t t)"

fun explode_size :: "nat \<Rightarrow> tree0 \<Rightarrow> nat" where
"explode_size n t = 2^n * (nodes t) + (2^n-1)"

  
lemma "nodes (explode n t) = explode_size n t"
  apply(induction n arbitrary: t)
  apply(auto simp add: algebra_simps)
  done

(* Exercise 2.11 *)
datatype exp = Var | Const int | Add exp exp | Mult exp exp

fun eval :: "exp \<Rightarrow> int \<Rightarrow> int" where
"eval Var x = x" |
"eval (Const a) x = a" | 
"eval (Add e1 e2) x = (eval e1 x) + (eval e2 x)" |
"eval (Mult e1 e2) x = (eval e1 x) * (eval e2 x)"

fun evalp :: "int list \<Rightarrow> int \<Rightarrow> int" where 
"evalp [] x = 0" |
"evalp (c # cfs) x = c + x * (evalp cfs x) " 


(* TODO: coeffs *)


end

