using StableExpr
using StableExpr.TermInterface
using Test
using Serialization
using Metatheory
using Metatheory.Rules: instantiate

using StableExpr: NodeID
@inline Metatheory.car(t::NodeID) = operation(t)
@inline Metatheory.cdr(t::NodeID) = arguments(t)

# exprs = deserialize("small.jls")

nc::NodeCache = NodeCache()

for f in (:exprhead, :operation, :arity, :arguments, :istree)
    @eval TermInterface.$(f)(id::NodeID) = TermInterface.$(f)(nc.nodes[id.id])
end
Base.show(io::IO, id::NodeID) = print(io, "NodeID($(id.id)): ", StableExpr.expr(nc, id))
TermInterface.similarterm(T::NodeID, args...; kwargs...) = TermInterface.similarterm(nc, T, args...; kwargs...)

function Base.isequal(ni::NodeID, val::T)  where {T<:Integer}
    on = nc[ni]
    (on.head == :integer) && (T(on.v) == val)
end

# for f in (:head, :arity, :children, :arguments, :operation, :iscall, :isexpr)
#     @eval TermInterface.$(f)(id::NodeID) = TermInterface.$(f)(nc.nodes[id.id])
# end
# TermInterface.maketerm(T::Type{NodeID}, args...) = TermInterface.maketerm(nc, T, args...)




r = @rule 2(~x) --> ~x + ~x
expr = :(2z)
r(expr)
ex = get!(nc, expr)
r(ex)

exprhead(ex) == exprhead(expr)
operation(ex) == operation(expr)
operation(ex) == operation(expr)
arity(ex) == arity(expr)
length(arguments(ex)) == length(arguments(expr))



r = @rule sin(2(~x)) --> 2sin(~x)*cos(~x)
expr = :(sin(2z))
r(expr)

ex = get!(nc, expr)
r(ex)


r = @rule sin(~x + ~y) --> sin(~x)*cos(~y) + cos(~x)*sin(~y);
expr = :(sin(x + y))
ex = get!(nc, expr)
r(expr)
r(ex)
