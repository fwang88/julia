*******************
Julia Functions
*******************

.. currentmodule:: Base

This document will explain how functions, method definitions, and method tables work.

Method Tables
-------------

Every function in Julia is a generic function. A generic function is conceptually a single
function, but consists of many definitions, or methods. The methods of a generic
function are stored in a method table.
Method tables (type ``MethodTable``) are associated with ``TypeName``\s. A ``TypeName``
describes a family of parameterized types. For example ``Complex{Float32}`` and
``Complex{Float64}`` share the same ``Complex`` type name object.

All objects in Julia are potentially callable, because every object has a type, which
in turn has a ``TypeName``.


Function calls
--------------

Given the call ``f(x,y)``, the following steps are performed: first, the method table
to use is accessed as ``typeof(f).name.mt``. Second, an argument tuple type is formed,
``Tuple{typeof(f), typeof(x), typeof(y)}``. Note that the type of the function itself
is the first element. This is because the type might have parameters, and so needs to
take part in dispatch. This tuple type is looked up in the method table.

This dispatch process is performed by ``jl_apply_generic``, which takes two arguments:
a pointer to an array of the values f, x, and y, and the number of values (in this
case 3).


Adding methods
--------------

Given the above dispatch process, conceptually all that is needed to add a new
method is (1) a tuple type, and (2) code for the body of the method.
``jl_method_def`` implements this operation.
``jl_first_argument_datatype`` is called to extract the relevant method table
from what would be the type of the first argument. This is much more complicated
than the corresponding procedure during dispatch, since the argument tuple
type might be abstract. For example, we can define::

    (::Union{Foo{Int},Foo{Int8}})(x) = 0

which works since all possible matching methods would belong to the same method
table.


Creating generic functions
--------------------------

Since every object is callable, nothing special is needed to create a generic
function. Therefore ``jl_new_generic_function`` simply creates a new singleton
(0 size) subtype of ``Function`` and returns its instance.
A function can have a mnemonic "display name" which is used in debug info and
when printing objects. For example the name of ``Base.sin`` is ``sin``. By
convention, the name of the created *type* is the same as the function name,
with a ``#`` prepended. So ``typeof(sin)`` is ``Base.#sin``.


Closures
--------

A closure is simply a callable object with field names corresponding to
captured variables. For example, the following code::

    function adder(x)
        return y->x+y
    end

is lowered to (roughly)::

    immutable ##1{T}
        x::T
    end

    (_::##1)(y) = _.x + y

    function adder(x)
        return ##1(x)
    end


Constructors
------------

A constructor call is just a call to a type. The type of most types is ``DataType``,
so the method table for ``DataType`` contains most constructor definitions.
One wrinkle is the fallback definition that makes all types callable via ``convert``::

    (::Type{T}){T}(args...) = convert(T, args...)::T

In this definition the function type is abstract, which is not normally supported.
To make this work, all subtypes of ``Type`` (``Type``, ``TypeConstructor``, ``Union``, and
``DataType``) currently share a method table via special arrangement.
