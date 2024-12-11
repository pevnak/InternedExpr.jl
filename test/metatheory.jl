using StableExpr
using StableExpr.TermInterface
using Test
using Serialization
using Metatheory
using Metatheory.Rules: instantiate

using StableExpr: NodeID

exprs = deserialize("small.jls")

nc::NodeCache = NodeCache()

for f in (:head, :arity, :children, :arguments, :operation, :iscall, :isexpr)
    @eval TermInterface.$(f)(id::NodeID) = TermInterface.$(f)(nc.nodes[id.id])
end
TermInterface.maketerm(T::Type{NodeID}, args...) = TermInterface.maketerm(nc, T, args...)



r = @rule sin(2(~x)) --> 2sin(~x)*cos(~x)
expr = :(sin(2z))
r(expr)

ex = get!(nc, expr)
r(ex)

r.matcher_left(ex, (bindings...) -> instantiate(ex, r.right, bindings), r.stack)

r = @rule sin(~x + ~y) --> sin(~x)*cos(~y) + cos(~x)*sin(~y);
ex = get!(nc, :(sin(x + y)))
r(ex)
