module Constraints

import Base: getindex, 
setindex!, 
convert,
==, <, <=, >, >=, +, -, *, /,
size, length 

import DataStructures: OrderedDict

abstract Sealed

type SealedArray <: Sealed
    data::SubArray
    dims
    touched::Array{Bool}
end

function SealedArray(data_view::SubArray, dims)
    touched = reshape(falses(length(data_view)), dims)
    SealedArray(data_view::SubArray, dims, touched)
end

function getindex(s::SealedArray, key...)
    s.touched[key...] = true
    if length(key) > 1
        index = key[1]
        for i = 2:length(key)
            index += (key[i] - 1) * s.dims[i-1]
        end
#         @show key
#         @show s.dims
#         @show index
        return s.data[index]
    else
        return s.data[key[1]]
    end
#     s.data[sub2ind(s.dims, key...)]
end

function setindex!(s::SealedArray, value, key...)
    s.data[sub2ind(s.dims, key...)] = value
end

function seal!(s::SealedArray)
    s.touched[:] = false
end

for op in [size, length]
    op(s::SealedArray) = op(s.data)
end

type Constraint
    vars::Vector{Symbol}
    func::Function
    estimated_quality::Number
    Constraint(vars::Vector{Symbol}, func::Function) = new(vars, func, 0)
end

immutable Domain
    lower::Array{Int}
    upper::Array{Int}
end

immutable Variable
    name::Symbol
    domain::Domain
end

length(v::Variable) = length(v.domain.lower)

type Problem
    vars::Vector{Variable}
    constraints::Vector{Constraint}
end

function Problem()
    Problem(Variable[], Constraint[])
end

function addVariable!(p::Problem, name::Symbol, lower::Array{Int}, upper::Array{Int})
    @assert length(upper) == length(lower)
    upper = reshape(upper, size(lower))
    push!(p.vars, Variable(name, Domain(lower, upper)))
    name
end
 
function addConstraint!(p::Problem, vars::Vector{Symbol}, func::Function)
    push!(p.constraints, Constraint(vars, func))
end

addConstraint!(p::Problem, var::Symbol, func::Function) = addConstraint!(p, [var], func)
    
typealias PotentialSolution Dict{Symbol, SealedArray}
typealias Solution Dict{Symbol, Array}

num_variables(sol::PotentialSolution) = sum([length(var) for (key, var) in sol])

type Results
    solutions::Vector{Solution}
    num_nodes_explored
end

function collect_domains(vars::Vector{Variable})
    total_vars = sum([length(v) for v in vars])
    min = Array(Int, total_vars)
    max = Array(Int, total_vars)
    offset = 0
    for v in vars
        numvar = length(v)
        min[offset+(1:numvar)] = v.domain.lower[:]
        max[offset+(1:numvar)] = v.domain.upper[:]
        offset += numvar
    end
    min, max
end

function min_solution(vars::Vector{Variable})
    PotentialSolution(zip([v.name for v in vars],
    [SealedArray(copy(v.domain.lower)) for v in vars]))
end
    
function choose_increment_order(prob::Problem, potential_solution::PotentialSolution)
    numvar = num_variables(potential_solution)
    touched = Array(Bool, numvar)
    increment_order = 1:numvar
    for constraint in prob.constraints
        seal!(potential_solution)
        constraint.func([potential_solution[v] for v in constraint.vars]...)
        check_seals!(touched, potential_solution)
        constraint.estimated_quality = numvar - sum(touched)
    end    

    sort!(prob.constraints, by=c->c.estimated_quality, rev=true)
    cumulative_touches = falses(size(touched))
    for constraint in prob.constraints
        seal!(potential_solution)
        constraint.func([potential_solution[v] for v in constraint.vars]...)
        check_seals!(touched, potential_solution)
        cumulative_touches = cumulative_touches | touched
        increment_order = increment_order[sortperm(cumulative_touches[increment_order])]
    end
    increment_order
end

function create_solution_view(prob::Problem, solution_data)
    potential_solution = PotentialSolution()
    offset = 0
    for v in prob.vars
        subview = sub(solution_data, offset+(1:length(v)))
        potential_solution[v.name] = SealedArray(subview, size(v.domain.lower))
        offset += length(v)
    end
    potential_solution
end

function solve(prob::Problem, max_solutions=Inf)
    lower, upper = collect_domains(prob.vars)
    @assert length(lower) == length(upper)
    @assert length(prob.constraints) > 0
    numvar = length(lower)
    touched = Array(Bool, numvar)
    solution_data = copy(lower)
    solutions = Solution[]
    num_satisfied_constraints = 0
    finished = false
    increment_index = 0
    num_nodes_explored = 1
    iteration = 0
    # exploring = true 
    solution_ok = true

    potential_solution = create_solution_view(prob, solution_data)
    increment_order = choose_increment_order(prob, potential_solution)

    
    while length(solutions) < max_solutions && !finished
        # @show potential_solution[:poses].data
        if iteration % 1 == 0
            exploring = true
        else
            exploring = false
        end
        
        increment_index = 0
        solution_ok = true
        for constraint in prob.constraints
            seal!(potential_solution)
            args = [potential_solution[v] for v in constraint.vars]
            if constraint.func(args...)
                constraint.estimated_quality = 0
            else
                solution_ok = false
                check_seals!(touched, potential_solution)
                constraint.estimated_quality = findfirst(touched[increment_order])
            end
            if !solution_ok
                increment_index = max(increment_index, constraint.estimated_quality)
                if !exploring
                    break
                end
            end
        end
        
        if exploring
            sort!(prob.constraints, by=c->c.estimated_quality, rev=true)
        end
        
        if solution_ok
            push!(solutions, extract_solution(potential_solution))
            increment_index = 1
        end
        
        @assert increment_index > 0
        for i = 1:increment_index-1
            solution_data[increment_order[i]] = lower[increment_order[i]]
        end
        solution_data[increment_order[increment_index]] += 1
        for i = increment_index:length(lower)-1
            j = increment_order[i]
            if solution_data[j] > upper[j]
                solution_data[j] = lower[j]
                solution_data[increment_order[i+1]] += 1
            else
                break
            end
        end
        if solution_data[increment_order[numvar]] > upper[increment_order[numvar]]
            finished = true
            break
        end
        num_nodes_explored += 1

        iteration += 1
    end
    Results(solutions, num_nodes_explored)
end
    
function seal!(potential::PotentialSolution) 
    for (name, var) in potential
        seal!(var)
    end
end

function check_seals!(touched::Vector{Bool}, potential::PotentialSolution)
    offset = 0
    for (k, v) in potential
        numel = length(v.touched)
        for j = 1:numel
            touched[offset+j] = v.touched[j]
        end
        offset += numel
    end
end

function extract_solution(solution::PotentialSolution)
    result = Dict(zip(keys(solution), map(v -> reshape(copy(v.data), v.dims), values(solution))))
end
    
end

import Constraints