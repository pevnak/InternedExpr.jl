module StableExpr
using Reexport
using TermInterface
using Base.ScopedValues

function intern! end

include("onlynode.jl")
export OnlyNode, LeafNode, NodeCache, expr, intern!


function lookup_pat end
function maybelock! end

include("utils.jl")
export @timer
export @iftimer
export @timerewrite
export @matchable

include("Patterns.jl")
@reexport using .Patterns
include("ematch_compiler.jl")
@reexport using .EMatchCompiler

include("matchers.jl")
include("Rules.jl")
@reexport using .Rules
include("Syntax.jl")
@reexport using .Syntax


include("onlynodes_rules.jl")
include("scoping.jl")


end # module StableExpr
