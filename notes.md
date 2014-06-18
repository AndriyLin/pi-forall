--- **06/16/2014 Morning** ---

So the instructor, Stephanie Weirich, is married to another instructor this morning, Steve Zdancewic.. 贤伉俪

-----

## A Simple Core language with Type in Type

Let's consider a simple dependently-typed lambda calculus. What should it
contain? At the bare minimum we can start with the following five forms:

     a,A ::= x       - variables 
         \x. a       - lambda expressions (anonymous functions)
         a b         - function applications
         (x:A) -> B  - dependent function type, aka Pi
         Type        - the 'type' of types

	注: (x:A) -> B is actually πx : A . B, just like forall (x : A), B
	里头 B may contain x


Note that we are using the *same* syntax for expressions and types. For
clarity, I'll used lowercase letters `a` for expressions and uppercase letters
for their types `A`

Note that lambda and pi above are *binding forms*. They bind the variable 
`x` in `b` and `B` respectively

### When do expressions in this language type check?

We define the type system for this language using an inductively defined
relation. This relation is between an expression, its type, and a typing
context.

     G |- a : A

The typing context is an ordered list of assumptions about the types of
variables. 

注：说有两种解读方式：

1.	a has type A
2.	by polymorphism, A has a proof a


### An initial set of typing rules - Variables and Functions

If we know a variable's type because it is in the typing context, then that is
its type:

       x : A in G
      ----------- var 
      G |- x : A

Functions get function types

        G, x:A |- a : B     
	 ---------------------------------    lambda
     G |- \x.a : (x:A) -> B

注：这里是dependent types


### Example: Polymorphic identity functions

注：到这里发现她就是按照整个notes的结构在讲

Note that the variable x is allowed to appear in `B`. Why is this useful? Well
it gives us *parametric polymorphism* right off the bat.  In Haskell, we 
write the identity function as follows:

       id :: a -> a
       id x = x

and Haskell automatically generalizes it to work for *all* types. 
We can do that here, except that we need to explicitly use lambda 
to make this function polymorphic. Instead of Haskell's 

       forall a. a -> a
		 
we will write the type of the polymorphic identity function as

       (x:Type) -> (y : x) -> x
		 
The fact that the type of `x` is `Type` means that `x` is a type variable. Again,
in this language we don't have a syntactic distinction between types and
terms (or expressions). Types are anything of type `Type`.  Expressions are 
things of type `A` where `A` has type `Type`.

          --------------------- var
           x:Type, y:x |- y : x
        ----------------------------- lambda
         x:Type |- y : (y : x) -> x
     ------------------------------------------ lambda
      |- \x. \y. y : (x:Type) -> (y : x) -> x


注：所以说，dependent types实际上就是polymorphism吗？！据Stephanie, dependent types subsumes polymorphism, 有一些东西是dependent types能做而polymorphism不能的。

dependent types里比polymorphism多一些，里头可以有computation。而像SystemF这样的polymorphism相当于在STLC上加上forall type 这样的东西，而dependent types里只要 (c : Type) -> ... 就可以

然后dependent types里可以有一些computation, 甚至可以有expression -> Type的function，这都是polymorphism做不到的


In pi-forall, we should eventually be able to write

     id : (x:Type) -> (y : x) -> x
	  id = \x. \y. y

or even (with some help from the parser)

     id : (x:Type) -> x -> x
     id = \x y . y 

### More typing rules - Types

注：以上这样写的好处就是比较灵活，不过只有上述规则的话，有一些不想要的program也能type check呀，所以：

Actually, I lied.  The real typing rule that we want for lambda 
has an additional precondition. We need to make sure that when we 
add assumptions to the context, those assumptions really are types. 
Otherwise, the rules would allow us to derive this type for the 
polymorphic lambda calculus:

     |- \x.\y. y : (x: 3) -> (y:x) -> x

So the real rule has an extra precondition that checks to make sure that 
A is actually a type. 

       G, x:A |- a : B       G |- A : Type
	 ----------------------------------------    lambda
     G |- \x.a : (x:A) -> B

This precondition means that we need some rules that conclude that 
types are actually types. For example, the type of a function is a 
type, so we will declare it with this rule (which also ensures that the
domain and range of the function are also types).

    G |- A : Type     G, x:A |- B : Type
    -------------------------------------- pi
     G |- (x:A) -> B : Type
	  
	  
Likewise, for polymorphism we need this, rather perplexing rule:	  
	  
	  ----------------  type
	  G |- Type : Type

注：就是这里和coq不同的，因此inconsistent, coq的话会 Type_i : Type_i+1，但是太麻烦了，这里就全部collapse了

Because the type of the polymorphic identity function starts with 
`(x:Type) -> ...` the `pi` rule means that `Type` must be a type for this pi
type to make sense. We declare this by fiat using the type : type rule. 

Note that, sadly, this rule make our language inconsistent as a
logic. Girard's paradox

### More typing rules - Application

Application requires that the type of the argument matches the domain type of
the function. However, not that because the type B could have x free in it, we
need to substitute the argument for x in the result.

      G |- a : (x:A) -> B 
		G |- b : A
    ---------------------------  app
	   G |- a b : B { b / x }

注：in STLC, a b 的结果 is of type B, 但是这里是dependent types, 所以需要substitution

注：在这样dependent types下，A -> B 其实就是 (x : A) -> B 的语法糖，当x不重要的时候


### Example: applying the polymorphic identity function

In pi-forall we should be able to apply the polymorphic identity function to
itself. When we do this, we need to first provide the type of id, then we can
apply id to id.

    idid : ((x:Type) -> (y : x) -> x) 
    idid = id ((x:Type) -> (y : x) -> x) id

### Example: Church booleans

Because we have (impredicative) polymorphism, we can *encode* familiar types,
such as booleans. The idea behind this encoding is to represent terms by their
eliminators. In other words, what is important about the value true? The fact
that when you get two choices, you pick the first one.  Likewise, false
"means" that with the same two choices, you should pick the second one.
With parametric polymorphism, we can give the two terms the same type, which
we'll call bool. 

    bool : Type
    bool = (x : Type) -> x -> x -> x

    true : bool
    true = \x . \y. \z. y
	 
    false : bool
    false = \x. \y. \z. z

Thus, a conditional expression just takes a boolean and returns it.

    cond : bool -> (x:Type) -> x -> x -> x
    cond = \ b . b 

### Example' : Church And (即兴添加的样子)

	and : Type -> Type -> Type
	and = \p. \q. (c : Type) -> (p -> q -> c) -> c

	注：有人回答到这个：
	or = \p. \q. (c : Type) -> (p -> c) -> (q -> c) -> c
	Stephanie说这个是or
	我现在的理解是：and表示both，就是俩都要考虑到function f中，而or是either，考虑一个就好

	conj : (p : Type) -> (q : Type) -> p -> q -> and p q
	conj = \p. \q. \x. \y. \c. \f. f x y
							这里对应(c : Type)
								这里对应(p -> q -> c)
									这里对应 c

	// example
	proj1 : (p : Type) -> (q : Type) -> and p q -> p
	proj1 = \p. \q. \a. a p (\x. \y. x)
					a的类型是and p q
						and p q其实就是(c : Type) -> (p -> q -> c) -> c
						   p对应的是c : Type
						     这个f对应的是(p -> q -> c)

	// example 2
	proj1 : (p : Type) -> (q : Type) -> and p q -> q
	proj1 = \p. \q. \a. a q (\x. \y. y)

	and_commutes : (p : Type) -> (q : Type) -> and p q -> and q p
	and_commutes = \p. \q. \a. conj q p (proj2 p q a) (proj1 p q a)
	// 上边这个就make sense了


注：为啥要c呢？we want to do anything with x & y, f is like doing anything and can return anything (that is, c).

注：and是操作types的


# From typing rules to a typing algorithm

注：在以上定义的type rules中，lambda rule里没有说明\x. __中x的type，所以需要inference


So the rules that we have developed so far are great for saying *what* terms
should type check, but they don't say *how*.  In particular, we've developed
these rules without thinking about how we would implement them.

A type system is called *syntax-directed* if it is readily apparent how to
turn the typing rules into code. In otherwords, we would like to implement the 
following function (in Haskell), that when given a term and a typing context 
produces the type of the term (if it exists).

    inferType :: Term -> Ctx -> Maybe Type

Let's look at our rules. Is this straightforward? For example, for the
variable rule as long as we can lookup the type of a variable in the context, 
we can produce its type. 

    inferType (Var x) ctx = Just ty when
	      ty = lookupTy ctx x
			
Likewise typing for Type is pretty straightforward.

    inferType Type ctx = Just Type

The only stumbling block for the algorithm is the lambda rule. The type
`A` comes out of thin air. What could it be?

There's actually an easy fix to turn our current system into an algorithmic
one. We just annotate lambdas with the types of the abstracted variables. 
But perhaps this is not what we want to do. 

Look at our example code: the only types that we wrote were the types of
definitions. It's good style to do that, and maybe if we change our point of
view we can get away without those argument types. 

# A Bidirectional type system

Let's redefine the system using two judgments: the standard judgement that we
wrote above, called type inference, but make it depend on a checking
judgement, that let's us take advantage of known type information.

    G |- a => A    inferType     in context G, infer that a has type A
	 
    G |- a <= A    checkType     in context G, check that a has type A


We'll go back to some of our existing rules. For variables, we can just change
the colon to an inference arrow. The context tells us the type to infer.

       x : A in G
      ----------- var 
      G |- x => A
		
On the other hand, we should check lambda expressions against a known type. If that 
type is provided, we can propagate it to the body of the lambda expression. We also 
know that we want A to be a type.		

     G, x:A |- a <= B       G |- A <= Type
	 ----------------------------------------    lambda
     G |- \x.a <= (x:A) -> B		((x:A) -> B is given, we just check a against this)

Applications can be in inference mode (in fact, checking mode doesn't help.)
Here we must infer the type of the function, but once we have that type, we
may to use it to check the type of the argument.
	  
      G |- a => (x:A) -> B 		(后头有说，缺少lambda的inference rule，但是var什么的就可以）
		G |- b <= A
    ---------------------------  app
	   G |- a b => B { b / x }	  

注：我想写成下边这个，但是应该就不行：

      G |- a <= (x:A) -> B		(this is probably not OK, since we don't know B)
		G |- b => A
    ---------------------------  app
	   G |- a b => B { b / x }

注：inference is like: given G, a, return a type A. checking is like: given G, a, A, return true/false

For types, it is apparent what their type is, so we will just continue to infer that.

    G |- A => Type     G, x:A |- B => Type
    -------------------------------------- pi
     G |- (x:A) -> B => Type

	  ----------------  type
	  G |- Type => Type

Notice that this system is fairly incomplete. There are inference rules for
every form of expression except for lambda. On the other hand, only lambda
expressions can be checked against types.  We can make checking more
applicable by the following rule:

       G |- a => A
		 -------------  (a does not have a checking rule)
		 G |- a <= A 

注：她在课上写的是这个：

       G |- a => A      A = B
		 ----------------------  (a does not have a checking rule)
		 G |- a <= B

which allows us to use inference whenever checking doesn't apply.


注：from inference to checking, 但是 from checking to inference就没有意义了，not syntax-directed:

	G |- a <= A     A = B
	----------------------
	G |- a => B

	If written like this, A is unknown, we cannot get A out of the air, (that's why it's not syntax-directed)

注：然后她说 we are missing something, 还是app rule和lambda rule的配合问题：

	ex1 = (\x. x) (\y. y) 这个就不行

注：她说有beta reduction的program都没有办法通过这个bidirectional的system type check呀！


Let's think about the reverse problem a bit. There are programs that the checking
system won't admit but would have been acceptable by our first system. What do
they look like?

Well, they involve applications of explicit lambda terms: （注：所以说只要用let什么bind起来就没问题啦？）

       |- \x.x : bool -> bool     |- true : bool
      ------------------------------------------  app
       |- (\x.x) true : bool

This term doesn't type check in the bidirectional system because application
requires the function to have an inferable type, but lambdas don't.

However, there is not that much need to write such terms in programs. We can
always replace them with something equivalent by doing the beta-reduction (in
this case, just true).

In fact, the bidirectional type system has the property that it only checks
terms in *normal* form, i.e. those that do not contain any reductions. If we
would like to add non-normal forms to our language, we can add annotations:

        G |- a <= A 
	  ------------------ annot
	  G |- (a : A) => A

The nice thing about the bidirectional system is that it reduces the number of
annotations that are necessary in programs that we want to write. As we will see, 
checking mode will be even more important as we add more terms to the language.

A not so desirable property is that the bidirectional system is not closed
under substitution. The types of variables are always inferred.  This is
particularly annoying for the application rule when replace a variable
(inference mode) with another term that is correct only in checking mode.  One
solution to this problem is to work with *hereditary substitutions*,
i.e. substitutions that preserve normal forms.

Alternatively, we can solve the problem through *elaboration*, the output 
of a type checker will be a term that works purely in inference mode.


### References 

* Cardelli, [A polymorphic lambda calculus with Type:Type](http://www.hpl.hp.com/techreports/Compaq-DEC/SRC-RR-10.pdf)
* Augustsson, [Cayenne -- a Language With Dependent Types](http://dl.acm.org/citation.cfm?id=289451)
* A. Löh, C. McBride, W. Swierstra, [A tutorial implementation of a dependently typed lambda calculus](http://www.andres-loeh.de/LambdaPi/)
* Andrej Bauer, [How to implement dependent type theory](http://math.andrej.com/2012/11/08/how-to-implement-dependent-type-theory-i/)

    
