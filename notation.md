
I would like to be able to use the implicit and typeclass machinery from my program.

# Implicits

```
\begin{notation}
Let $C$,$D$ be categories and let $F$ be a functor from $C$ to $D$. Let $c$,$d$ be objects of $C$ and let $f$ be a morphism from $c$ to $d$.

Let $F(f)$ stand for $\map{C}{D}{F}{c}{d}{f}$.
\end{notation}
```

This simply should simply define implicit arguments for C,D,c and d. Should work pretty well, since they can be inferred.

One would take the free variables of $F(f)$ and add them as explicit arguments and then all the other variables will be implicit and will have to satisfy the predicate defined by the assumptions.

We will check that the proposition defined by the assumptions `isDefEq` to `True`, so that inferring its proof will simply use `True.intro`.

# Typeclasses

```
\begin{notation} \label{comp}
Let $G$ be a group. Let $g$, $h$ be elements of $G$.

Let $g \circ h$ stand for $grp_operation{G}{g}{h}$.
\end{notation}
```

In this case, $G$ can't be inferred by unification, since we don't know which group structure on the underlying set of $G$ to use. It needs to be synthethized by using a finite list of instances. We will somehow need to mark the free variable $G$ as a parameter of an instance of a typeclass (in this case, it should be `comp`).

The problem is that we linguistically can't distinguish between arguments to be inferred by typeclass resolution and arguments inferred by unification.

Moreover, the mechanisms of implicit arguments and typeclass declarations are structurally very different.

This is hard, I should wait until I have started writing actual CNL code.
