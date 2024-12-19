using InternedExpr
using InternedExpr.TermInterface
using Test
using Serialization
using SymbolicUtils
using SymbolicUtils: car, cdr, islist, iscall

using InternedExpr: NodeID
@inline SymbolicUtils.car(t::NodeID) = operation(t)
@inline SymbolicUtils.cdr(t::NodeID) = arguments(t)

exprs = deserialize("small.jls")

for f in (:head, :arity, :children, :arguments, :operation, :iscall, :isexpr)
    @eval TermInterface.$(f)(id::NodeID) = TermInterface.$(f)(nc.nodes[id.id])
end

# asdfasdf


nc = NodeCache()

# Let's test the enrollement
map(e -> get!(nc, e), exprs);


# Let's test term interface
ex = get!(nc, :(f(a, b)))
@test head(ex) == :f
@test children(ex) == [:f, nc[LeafNode(:a)], nc[LeafNode(:b)]]
@test operation(ex) == :f
@test arguments(ex) == [nc[LeafNode(:a)], nc[LeafNode(:b)]]
@test isexpr(ex) == true
@test iscall(ex)

@test car(ex) == car(:(f(a, b)))
@test cdr(ex) == [nc[LeafNode(:a)], nc[LeafNode(:b)]]


using SymbolicUtils: @timer, assoc, drop_n

r = @rule sin(~x + ~y) => sin(~x)*cos(~y) + cos(~x)*sin(~y);
ex = get!(nc, :(sin(x + y)))
r(ex)

@syms x y;
nc = NodeCache();
sx = sin(x + y);
ex = get!(nc, :(sin(x + y)));
head(ex)
head(sx)

r(sin(cos(x) + sin(y)))

rhs = r.rhs
_success(bindings, n) = n == 1 ? (@timer "RHS" rhs(assoc(bindings, :MATCH, term))) : nothing
r.matcher(_success, (ex,), SymbolicUtils.EMPTY_IMMUTABLE_DICT)
r.matcher(_success, (sx,), SymbolicUtils.EMPTY_IMMUTABLE_DICT)

# @ SymbolicUtils ~/.julia/packages/SymbolicUtils/jf8aQ/src/matchers.jl:89

islist(ex) == islist(sx)
iscall(car(ex)) == iscall(car(sx))

using SymbolicUtils: term_matcher
function SymbolicUtils.matcher(val::Any)
    @show iscall(val)
    iscall(val) && return term_matcher(val)
    function literal_matcher(next, data, bindings)
        @show islist(data)
        @show (car(data), val)
        @show isequal(car(data), val)
        islist(data) && isequal(car(data), val) ? next(bindings, 1) : nothing
    end
end

data = sx 
function SymbolicUtils.term_matcher(success, data, bindings)
    !islist(data) && return nothing
    !iscall(car(data)) && return nothing

    function loop(term, bindings′, matchers′) # Get it to compile faster
        @show term
        if !islist(matchers′)
            if  !islist(term)
                return success(bindings′, 1)
            end
            return nothing
        end
        car(matchers′)(term, bindings′) do b, n
            @show ("inner: ",n, term)
            loop(drop_n(term, n), b, cdr(matchers′))
        end
    end
    @show car(data)
    loop(car(data), bindings, matchers) # Try to eat exactly one term
end

r = @rule sin(~x + ~y) => sin(~x)*cos(~y) + cos(~x)*sin(~y);
matchers = r.matcher.matchers
term_matcher(_success, (ex,), SymbolicUtils.EMPTY_IMMUTABLE_DICT)
term_matcher(_success, (sx,), SymbolicUtils.EMPTY_IMMUTABLE_DICT)

Base.isequal(x::Symbol,  ::typeof(sin)) = x == :sin
Base.isequal(x::Symbol,  ::typeof(+)) = x == :+
Base.sin(x::NodeID) = ....