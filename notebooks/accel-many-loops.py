#!/usr/bin/env python3
import islpy as isl
from islpy import *

def rearrange_pow(m):
    m = m.move_dims(dim_type.param, 0, dim_type.in_, 0, 1)
    s = m.range()
    m = s.unwrap()
    return m

# Return a map that is applied 0 or 1 times
def m01(m):
    mid = Map.identity(m.get_space())
    return m.union(mid).coalesce()

def msq(m):
    return m.apply_range(m).coalesce()
    
print("[x -> x + 1] 0/1d: %s " % m01(Map("{ [x] -> [x + 1] }")))
print("[x -> x + 1]^2:  %s " % msq(Map("{ [x] -> [x + 1] }")))

# Build a transitive closure operator that computes the transitive
# closure upto a certain power of 2
def transitive_closure_upto(m, pot):
    if pot == 0:
        return m01(m)
    else:
        return msq(transitive_closure_upto(m, pot - 1)).coalesce().coalesce()
    
print("[x -> x + 1] closure (2^64): %s " % transitive_closure_upto(Map("{ [x] -> [x + 1] }"), 64))

def power2d_complex_1():
    # increment i once j has stopped incrementing
    deltai =  "[i, ci, 0, 0, 0] -> [i, ci, 0, 0, 1] : ci >= 0 and i < 10"
    deltaj = "[i, ci, j, cj, 1] -> [i, ci, j+1, cj+1, 1] : ci >= 0 and cj >= 0 and j < 10"
    j2i = "[i, ci, j, cj, 1] -> [i+1, ci+1, 0, 0, 0] : ci >= 0 and i < 10 and cj >= 0 and j = 10"

    m0 = isl.Map("[k, l] -> {" + deltai + ";" + deltaj + ";" + j2i + "}")
    print("m0: %s" % m0)

    ISL_TRANSITIVE_CLOSURE = True
    if ISL_TRANSITIVE_CLOSURE: 
        (m, exact) = m0.transitive_closure() # -- transitive_closure_upto(m0, 3)
        assert(exact)
    else:
        m = m0
        m = m.coalesce()
    print("m after trans: %s"% m)

    delta = m.deltas()
    print("delta: %s" % delta)

    # p0 = count
    c = Constraint.alloc_equality(isl.LocalSpace.from_space(delta.get_space()))
    # k - ci = 0
    c = c.set_coefficient_val(dim_type.param, 0, 1)
    c = c.set_coefficient_val(dim_type.set, 1, -1)
    delta = delta.add_constraint(c)
    # l - cj = 0
    c = Constraint.alloc_equality(isl.LocalSpace.from_space(delta.get_space()))
    c = c.set_coefficient_val(dim_type.param, 1, 1)
    c = c.set_coefficient_val(dim_type.set, 3, -1)
    delta = delta.add_constraint(c)

    # k >= 0
    c = Constraint.alloc_inequality(isl.LocalSpace.from_space(delta.get_space()))
    c = c.set_coefficient_val(dim_type.param, 0, 1)
    delta = delta.add_constraint(c);


    # l >= 0
    c = Constraint.alloc_inequality(isl.LocalSpace.from_space(delta.get_space()))
    c = c.set_coefficient_val(dim_type.param, 1, 1)
    delta = delta.add_constraint(c);


    # project out the "count" dimension
    delta = delta.project_out(dim_type.set, 4, 1)

    # project out cj
    delta = delta.project_out(dim_type.set, 3, 1)
    # project out ci
    delta = delta.project_out(dim_type.set, 1, 1)


    print("delta after projection: %s" % delta)
    return delta.coalesce().coalesce()
    
def power2d_complex_2():
    # increment i once j has stopped incrementing
    deltai =  "[i, ci, j, cj] -> [i+1, ci+1, 0, 0] : ci >= 0 and cj >= 0 and i < 10 and j > i; [i, ci, j, cj] -> [i, ci, 0, cj] : ci >= 0 and cj >= 0 and i < 10 and j = i"
    deltaj = "[i, ci, j, cj] -> [i, ci, j+1, cj+1] : ci >= 0 and cj >= 0 and j < i"
    mj = isl.Map("[k, l] -> {" + deltaj + "}")
    mi = isl.Map("[k, l] -> {" + deltai + "}")
    print("mj: %s" % mj)
    print("mi: %s" % mi)

    # This now has accelerated j representation.
    mj = transitive_closure_upto(mj, 64).coalesce()
    mi = transitive_closure_upto(mi, 64).coalesce()
    print("transmj: %s" % mj)
    print("transmi: %s" % mi)


    m = mi.union(mj).coalesce()
    
    delta = m.deltas()
    c = Constraint.alloc_equality(isl.LocalSpace.from_space(delta.get_space()))
    # k - ci = 0
    c = c.set_coefficient_val(dim_type.param, 0, 1)
    c = c.set_coefficient_val(dim_type.set, 1, -1)
    delta = delta.add_constraint(c);

    # k >= 0
    c = Constraint.alloc_inequality(isl.LocalSpace.from_space(delta.get_space()))
    c = c.set_coefficient_val(dim_type.param, 0, 1)
    delta = delta.add_constraint(c);

    # l - cj = 0
    c = Constraint.alloc_equality(isl.LocalSpace.from_space(delta.get_space()))
    c = c.set_coefficient_val(dim_type.param, 1, 1)
    c = c.set_coefficient_val(dim_type.set, 3, -1)
    delta = delta.add_constraint(c);


    # l >= 0
    c = Constraint.alloc_inequality(isl.LocalSpace.from_space(delta.get_space()))
    c = c.set_coefficient_val(dim_type.param, 1, 1)
    delta = delta.add_constraint(c);

    delta = delta.project_out(dim_type.set, 3, 1)
    delta = delta.project_out(dim_type.set, 1, 1)

    return delta.coalesce()

    delta = m.deltas()
    print("delta: %s" % delta)
    # p0 = count
    c = Constraint.alloc_equality(isl.LocalSpace.from_space(delta.get_space()))
    # k - ci = 0
    c = c.set_coefficient_val(dim_type.param, 0, 1)
    c = c.set_coefficient_val(dim_type.set, 1, -1)
    # l - cj = 0
    c = c.set_coefficient_val(dim_type.param, 1, 1)
    c = c.set_coefficient_val(dim_type.set, 3, -1)

    print("\n\nc: %s" % c)
    delta = delta.add_constraint(c)
    print("delta after constraint: %s" % delta)
    # project out ci
    delta = delta.project_out(dim_type.set, 1, 1)
    # project out cj
    delta = delta.project_out(dim_type.set, 2, 1)

    print("delta after projection: %s" % delta)
    return delta
    
m = power2d_complex_1()
# m = power2d_complex_2()
print("FINAL: %s" % m)
