# -*- coding: utf-8 -*-
r"""
This module implements functionality for investigating rigidity and flexibility of graphs with a symmetry.

Methods
-------

**SymmetricFlexRiGraph**

{INDEX_OF_METHODS_SYMMETRIC_FLEXRIGRAPH}

**CnSymmetricFlexRiGraph**

{INDEX_OF_METHODS_CN_SYMMETRIC_FLEXRIGRAPH}

**CsSymmetricFlexRiGraph**

{INDEX_OF_METHODS_CS_SYMMETRIC_FLEXRIGRAPH}

AUTHORS:

-  Jan Legerský (2020-03-12): initial version
-  Jan Legerský (2022-05-19): Cs-symmetry added

TODO:

    - missing documentation of methods
    - missing doctests in methods
    - finish Cn-symmetry functionality (NACs, doc, classification)

WARNING:

    This module is still under development!

SymmetricFlexRiGraph
--------------------

"""

#Copyright (C) 2018 Jan Legerský
#
#This program is free software: you can redistribute it and/or modify
#it under the terms of the GNU General Public License as published by
#the Free Software Foundation, either version 3 of the License, or
#(at your option) any later version.
#
#This program is distributed in the hope that it will be useful,
#but WITHOUT ANY WARRANTY; without even the implied warranty of
#MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#GNU General Public License for more details.
#
#You should have received a copy of the GNU General Public License
#along with this program.  If not, see <https://www.gnu.org/licenses/>.

#from sage.all_cmdline import *   # import sage library
from sage.all import Graph, Set, ceil, sqrt, matrix, deepcopy, copy
from sage.all import Subsets, rainbow, show, binomial, RealField
from sage.all import var, solve, RR, vector, norm, CC
from sage.all import PermutationGroup, PermutationGroup_generic
from sage.groups.perm_gps.permgroup_element import is_PermutationGroupElement
from sage.all import pi, cos, sin, cartesian_product
import random
from itertools import chain

from sage.misc.rest_index_of_methods import doc_index, gen_thematic_rest_table_index
from sage.rings.integer import Integer


from .NAC_coloring import NACcoloring
from .flexible_rigid_graph import FlexRiGraph, FlexRiGraphWithCartesianNACs

    
    
class SymmetricFlexRiGraph(FlexRiGraph):
    r"""
    The class SymmetricFlexRiGraph is inherited from :class:`FlexRiGraph`.
    It represents a graph with a given symmetry.

    INPUT:

    - ``data``: provides the information about edges, see :class:`FlexRiGraph`..

    - ``symmetry`` -- `sage.graphs.graph.Graph <http://doc.sagemath.org/html/en/reference/groups/sage/groups/perm_gps/permgroup.html>`_
      that is a subgroup of the automorphism group of the graph, the list of its generators
      or a permutation generating the subgroup.

    TODO:
    
        examples
    """

    def __init__(self, data, symmetry, pos=None, name=None, check=True, verbosity=0):
        super(SymmetricFlexRiGraph, self).__init__(data, pos, name, check, verbosity)
        if isinstance(symmetry, PermutationGroup_generic):
            self._sym_group = symmetry
            self._sym_gens = self._sym_group.gens()
        elif isinstance(symmetry, list):
            self._sym_gens = symmetry
            self._sym_group = PermutationGroup(symmetry, domain=self.vertices(sort=False))
        elif is_PermutationGroupElement(symmetry):
            self._sym_gens = [symmetry]
            self._sym_group = PermutationGroup([symmetry], domain=self.vertices(sort=False))
        
        for gen in self._sym_gens:
            for u,v in self.edges(labels=False, sort=False):
                if not self.has_edge(gen(u), gen(v)):
                    raise ValueError('`symmetry must be a subgroup of the automorphism group of the graph or the list of its generators, not '
                                     + str(self._sym_group))                    


    def _repr_(self):
        return super(SymmetricFlexRiGraph, self)._repr_() + '\nwith the symmetry ' + str(self._sym_group)

    @staticmethod
    def is_cyclic_subgroup(subgroup):
        r'''
        Return if a group is cyclic, a generator and order.
        '''
        if subgroup.is_cyclic():
            order = subgroup.order()
            for gen in subgroup.gens():
                if gen.order() == order:
                    return (True, gen, order)
            for gen in subgroup:
                if gen.order() == order:
                    return (True, gen, order)
        return (False, None, None)

    @staticmethod
    def _cyclic_subgroups(group, order):
        r'''
        Return all cyclic subgroups of ``group`` with given ``order``.
        '''
        res_sbgrps = []
        for sbgrp in group.subgroups():
            cyclic, gen, n = SymmetricFlexRiGraph.is_cyclic_subgroup(sbgrp)
            if cyclic and n == order:
                res_sbgrps.append(gen)
        return res_sbgrps

class CnSymmetricFlexRiGraph(SymmetricFlexRiGraph):
    r"""
    This class is inherited from :class:`SymmetricFlexRiGraph`.
    It represents a graph with a given $\\mathcal{C}_n$ symmetry,
    namely, a cyclic subgroup of order `n` of the automorphism group of the graph
    such that
    
    - each partially invariant is invariant
    - the set of invariant vertices is independent.
    
    WARNING:
    
    Only $\\mathcal{C}_n$-symmetric NAC-colorings are considered in an instance of :class:`CnSymmetricFlexRiGraph`
    for parent methods! 
    For example, :meth:`FlexRiGraph.NAC_colorings()` returns the list of all  $\\mathcal{C}_n$-symmetric NAC-colorings
    of the graph.
    
    INPUT:

    - ``data``: provides the information about edges, see :class:`FlexRiGraph`..

    - ``symmetry`` -- `sage.graphs.graph.Graph <http://doc.sagemath.org/html/en/reference/groups/sage/groups/perm_gps/permgroup.html>`_
      that is a subgroup of the automorphism group of the graph or the list of its generator.
      The properties above must hold.

    TODO:
    
        - examples
        - check input as list of edges
    """
    def __init__(self, data, symmetry, pos=None, pos_sym=True, name=None, check=True, verbosity=0):
        super(CnSymmetricFlexRiGraph, self).__init__(data, symmetry, pos, name, check, verbosity)
        is_cyclic, gen, order = SymmetricFlexRiGraph.is_cyclic_subgroup(self._sym_group)
        if not is_cyclic:
            raise ValueError(str(self._sym_group) + ' is not a cyclic subgroup of the automorphism group of the graph.')
        if not CnSymmetricFlexRiGraph.is_Cn_symmetry(self, gen, order):
            raise ValueError(str(self._sym_group) + ' is not a Cn-symmetry of the graph.')
        self._sym_gens = [gen]
        self.omega = gen
        self.n = order
        self._edge_orbits = None
        self._vertex_orbits = None
        self._invariant_vertices = None
        self._NACs_computed = 'no'
        
        self._report('Vertex orbits: ' + str(self.vertex_orbits()), 2)
        if pos==None:
            pos_sym = False
            pos = {
                orbit[0]:self._pos[orbit[0]] for orbit in self.vertex_orbits()
                }
            for i, v in enumerate(self._invariant_vertices):
                pos[v] = (0, 0.1*i)
        if not pos_sym:
            self.set_symmetric_positions(pos)
         
    def vertex_orbits(self):
        r"""
        Return the orbits of vertices.
        
        EXAMPLES::
        
            sage: from flexrilog import CnSymmetricFlexRiGraph, GraphGenerator
            sage: G = GraphGenerator.CompleteGraphWithTrianglesAround(3, instance_CnSymmetricFlexRiGraph=True); G
            CnSymmetricFlexRiGraph with 9 vertices and 15 edges
            with the symmetry Permutation Group with generators [(0,1,2)(3,5,7)(4,6,8)]
            sage: G.vertex_orbits()
            [[0, 1, 2], [3, 5, 7], [4, 6, 8]]
            
        ::
            
            sage: G2 = CnSymmetricFlexRiGraph(G, PermutationGroup([[(1,2),(3,4),(5,8),(6,7)]])); G2
            CnSymmetricFlexRiGraph with 9 vertices and 15 edges
            with the symmetry Permutation Group with generators [(1,2)(3,4)(5,8)(6,7)]
            sage: G2.vertex_orbits()
            [[1, 2], [3, 4], [5, 8], [6, 7], [0]]

        """
        if self._vertex_orbits:
            return self._vertex_orbits
        
        self._vertex_orbits = []
        verts = {v:0 for v in self.vertices(sort=False)}
        for v in self.invariant_vertices():
            verts.pop(v)
        while verts:
            v = min(verts.keys())
            verts.pop(v)
            orbit = [v]
            for _ in range(1,self.n):
                w = self.omega(orbit[-1])
                orbit.append(w)
                verts.pop(w)
            self._vertex_orbits.append(orbit)
                
        self._vertex_orbits += [[v] for v in self.invariant_vertices()]

        return self._vertex_orbits
    
           
    def edge_orbits(self):
        r"""
        Return the orbits of edges.
        
        EXAMPLES::
        
            sage: from flexrilog import GraphGenerator
            sage: T = GraphGenerator.CompleteGraphWithTrianglesAround(2,instance_CnSymmetricFlexRiGraph=True); T
            CnSymmetricFlexRiGraph with the vertices [0, 1, 2, 3, 4, 5] and edges [(0, 1), (0, 2), (0, 3), (1, 4), (1, 5), (2, 3), (2, 5), (3, 4), (4, 5)]
            with the symmetry Permutation Group with generators [(0,1)(2,4)(3,5)]
            sage: T.edge_orbits()
            [[[4, 5], [2, 3]],
             [[0, 2], [1, 4]],
             [[3, 4], [2, 5]],
             [[1, 5], [0, 3]],
             [[0, 1]]]
             
        ::
            
            sage: G = GraphGenerator.CompleteGraphWithTrianglesAround(3,instance_CnSymmetricFlexRiGraph=True); G
            CnSymmetricFlexRiGraph with 9 vertices and 15 edges
            with the symmetry Permutation Group with generators [(0,1,2)(3,5,7)(4,6,8)]
            sage: G.edge_orbits()
            [[[1, 6], [8, 2], [0, 4]],
             [[8, 3], [6, 7], [4, 5]],
             [[3, 4], [5, 6], [8, 7]],
             [[0, 1], [0, 2], [1, 2]],
             [[2, 7], [1, 5], [0, 3]]]
             
        ::
            
            sage: from flexrilog import CnSymmetricFlexRiGraph
            sage: fold2syms = CnSymmetricFlexRiGraph.Cn_symmetries_gens(G,2)
            sage: G2 = CnSymmetricFlexRiGraph(G,fold2syms[0]); G2
            CnSymmetricFlexRiGraph with 9 vertices and 15 edges
            with the symmetry Permutation Group with generators [(1,2)(3,4)(5,8)(6,7)]
            sage: G2.edge_orbits()
            [[[3, 4]],
             [[1, 2]],
             [[0, 1], [0, 2]],
             [[1, 6], [2, 7]],
             [[0, 4], [0, 3]],
             [[5, 6], [8, 7]],
             [[8, 2], [1, 5]],
             [[8, 3], [4, 5]],
             [[6, 7]]]
        """
        if self._edge_orbits:
            return self._edge_orbits
        orbits = []
        for u,v in self.edges(labels=False, sort=False):
            orbit = [Set([u,v])]
            for _ in range(1,self.n):
                orbit.append(Set([self.omega(orbit[-1][0]), self.omega(orbit[-1][1])]))
            orbits.append(Set(orbit))
        self._edge_orbits = [[[u,v] for u, v in orbit] for orbit in Set(orbits)]
        return self._edge_orbits
    
        
    def invariant_vertices(self):
        r"""
        Return the invariant vertices.
        """
        if self._invariant_vertices:
            return self._invariant_vertices
        self._invariant_vertices = [v for v in self.vertices(sort=False) if len(self.omega.orbit(v))<self.n]
        return self._invariant_vertices
            
    
    def set_symmetric_positions(self, pos):
        r"""
        Given a dictionary of positions of one vertex from some orbits, the other vertices in the orbits are set symmetrically.
        """
        new_pos = {}
        for w in pos:
            for orbit in self.vertex_orbits():
                if w in orbit:
                    i = orbit.index(w)
                    for j, v in enumerate(orbit[i:]+orbit[:i]):
                        alpha = RR(2*pi*j/self.n)
                        new_pos[v] = matrix([[cos(alpha), -sin(alpha)],
                                             [sin(alpha), cos(alpha)]])* vector(pos[w])
                    break
        self.set_pos(new_pos)
                
    @doc_index("NAC-colorings")
    def _find_NAC_colorings(self, onlyOne=False, names=False):
        r"""
        Find Cn-symmetric NAC-colorings and store them in ``self._NAC_colorings``.
        
        WARNING:
            
            Currently, the option ``onlyOne`` is rather meaningless,
            since all NAC-colorings must be computed to get Cn-symmetric ones.
            
        TODO:
        
            ``onlyOne`` option if normal NACs work as an iterator.
        """
        from .symmetric_NAC_coloring import CnSymmetricNACcoloring
        FlexRiGraph._find_NAC_colorings(self, onlyOne=False, names=names)
        symmetric_NACs = []
        self._report('Sorting out Cn-symmetric NAC-colorings')
        for delta in self._NAC_colorings:
            delta_sym = CnSymmetricNACcoloring(self, delta, check=False)
            if delta_sym.is_Cn_symmetric():
                symmetric_NACs.append(delta_sym)
                if onlyOne:
                    break
                    self._NACs_computed = 'onlyOne'
        self._NAC_colorings = symmetric_NACs
    
    
    @doc_index("NAC-colorings")   
    def Cn_symmetric_NAC_colorings(self):
        r"""
        Alias for :meth:`NAC_colorings`.
        
        Return $\\mathcal{C}_n$-symmetric NAC-colorings.
        
        EXAMPLES::
        
            sage: from flexrilog import CnSymmetricFlexRiGraph, GraphGenerator
            sage: T = GraphGenerator.ThreePrismGraph()
            sage: Cn_symmetries = CnSymmetricFlexRiGraph.Cn_symmetries_gens(T, 2); Cn_symmetries
            [(0,1)(2,3)(4,5), (0,2)(1,4)(3,5), (0,5)(1,3)(2,4), (0,5)(1,4)(2,3)]
            sage: T_sym = CnSymmetricFlexRiGraph(T, Cn_symmetries[0])
            sage: T_sym.Cn_symmetric_NAC_colorings()
            [Cn-symmetric NAC-coloring with red edges 
            [[0, 3], [0, 4], [1, 2], [1, 5], [2, 5], [3, 4]] and blue edges [[0, 5], [1, 4], [2, 3]]]
        """
        return self.NAC_colorings()

    
    
    @staticmethod
    def is_Cn_symmetry(graph, sigma, n):
        r"""
        Return whether ``sigma`` generates a $\\mathcal{C}_n$-symmetry of the `graph`.
        """
        partially_inv = [v for v in graph.vertices(sort=False) if len(sigma.orbit(v))<n]
        if [v for v in partially_inv if len(sigma.orbit(v))>1]:
            return False
        if Graph(graph).is_independent_set(partially_inv):
            return True
        
    @staticmethod
    def Cn_symmetries_gens(graph, n):
        r"""
        Return the list of generators of Cn symmetries of the graph.
        
        An element $\\omega$ of order `n` of the automorphism group of the graph
        generates a $\\mathcal{C}_n$-symmetry of the graph if
        
        - each partially invariant is invariant
        - the set of invariant vertices is independent.
        
        EXAMPLES::
        
            sage: from flexrilog import CnSymmetricFlexRiGraph, GraphGenerator
            sage: T = GraphGenerator.ThreePrismGraph()
            sage: Cn_symmetries = CnSymmetricFlexRiGraph.Cn_symmetries_gens(T, 2); Cn_symmetries
            [(0,1)(2,3)(4,5), (0,2)(1,4)(3,5), (0,5)(1,3)(2,4), (0,5)(1,4)(2,3)]
        """
        
        res = []
        for sigma in SymmetricFlexRiGraph._cyclic_subgroups(graph.automorphism_group(), n):
            if CnSymmetricFlexRiGraph.is_Cn_symmetry(graph, sigma, n):
                res.append(sigma)
        return res
    
    @staticmethod    
    def Cn_symmetries_gens_according_isomorphic_orbits(G, n):
        r"""
        Return the generators of Cn-symmetries divided according to isomorphic orbits.
        
        An element $\\omega$ of order `n` of the automorphism group of the graph
        generates a $\\mathcal{C}_n$-symmetry of the graph if
        
        - each partially invariant is invariant
        - the set of invariant vertices is independent.
        
        OUTPUT:
        
        The output is the list of lists of generators - two generators are in the same
        list if there is a graph isomorphism mapping orbits of one generator to orbits of the other.
        
        EXAMPLES::
        
            sage: from flexrilog import CnSymmetricFlexRiGraph, GraphGenerator
            sage: T = GraphGenerator.ThreePrismGraph()
            sage: CnSymmetricFlexRiGraph.Cn_symmetries_gens_according_isomorphic_orbits(T, 2)
            [[(0,1)(2,3)(4,5), (0,2)(1,4)(3,5), (0,5)(1,3)(2,4)],
             [(0,5)(1,4)(2,3)]]
        """
        def gen2orbit_sets(gamma):
            Gsym = CnSymmetricFlexRiGraph(G, gamma)
            return Set([Set(orbit) for orbit in Gsym.vertex_orbits()])
        
        def orbits_image(tau, orbits):
            return Set([Set([tau(v) for v in orbit]) for orbit in orbits])
        
        autG = G.automorphism_group()
        symmetries = CnSymmetricFlexRiGraph.Cn_symmetries_gens(G, n)
        if symmetries==[]:
            return []
        res = {}
        for omega in symmetries:
            orbits = gen2orbit_sets(omega)
            for tau in autG:
                tau_orbits = orbits_image(tau, orbits)
                if tau_orbits in res:
                    res[tau_orbits].append(omega)
                    break
            else:
                res[tau_orbits] = [omega]
        return list(res.values())

    def _edges_with_same_color(self):
        r"""
        Return list of lists of edges that are necessarily colored the same in a Cn-symmetric NAC-coloring.
        """
        V = [tuple(sorted(e)) for e in self.edges(labels=False, sort=False)]
        E = []
        for tr_comp in self.triangle_connected_components():
            E += [[tuple(sorted(e)), tuple(sorted(f))] for e, f in zip(tr_comp[:-1], tr_comp[1:])]
        for orbit in self.edge_orbits():
            E += [[tuple(sorted(e)), tuple(sorted(f))] for e, f in zip(orbit[:-1], orbit[1:])]
        return [[[u,v] for u, v in comp] for comp in Graph([V, E], format='vertices_and_edges').connected_components(sort=False)]


class CnSymmetricFlexRiGraphCartesianNACs(CnSymmetricFlexRiGraph, FlexRiGraphWithCartesianNACs):
    r"""
    This class is inherited from :class:`CnSymmetricFlexRiGraph` and :class:`FlexRiGraphWithCartesianNACs`.
    Only Cn-symmetric cartesian NAC-colorings are computed.
    To speed this up comparing to computing all NAC-colorings followed by a check,
    opposite edges in a 4-cycle are forced to have the same color in NAC-colorings
    (by overriding :meth:`_edges_with_same_color`) as well as orbits of edges under the symmetry.
    """
    def _edges_with_same_color(self):
        r"""
        Return list of lists of edges that are necessarily colored the same in a Cn-symmetric NAC-coloring.
        """
        V = [tuple(sorted(e)) for e in self.edges(labels=False, sort=False)]
        E = []
        for tr_comp in self.triangle_connected_components():
            E += [[tuple(sorted(e)), tuple(sorted(f))] for e, f in zip(tr_comp[:-1], tr_comp[1:])]
        for orbit in self.edge_orbits():
            E += [[tuple(sorted(e)), tuple(sorted(f))] for e, f in zip(orbit[:-1], orbit[1:])]
            
        for a,b,c,d in self.four_cycles():
            E += [[tuple(sorted([a,b])), tuple(sorted([c,d]))], [tuple(sorted([a,d])), tuple(sorted([b,c]))]]
            
        return [[[u,v] for u, v in comp] for comp in Graph([V, E], format='vertices_and_edges').connected_components(sort=False)]


class CsSymmetricFlexRiGraph(SymmetricFlexRiGraph):
    r"""
    This class is inherited from :class:`SymmetricFlexRiGraph`.
    It represents a graph with a given $\\mathcal{C}_s$ symmetry,
    namely, a cyclic subgroup of order 2 of the automorphism group of the graph.
       
    INPUT:

    - ``data``: provides the information about edges, see :class:`FlexRiGraph`..

    - ``symmetry`` -- `sage.graphs.graph.Graph <http://doc.sagemath.org/html/en/reference/groups/sage/groups/perm_gps/permgroup.html>`_
      that is a subgroup of the automorphism group of the graph or the list of its generator.

    TODO:
    
        - examples
    """
    def __init__(self, data, symmetry, pos=None, pos_sym=False, name=None, check=True, verbosity=0):
        super(CsSymmetricFlexRiGraph, self).__init__(data, symmetry, pos, name, check, verbosity)
        is_cyclic, gen, order = SymmetricFlexRiGraph.is_cyclic_subgroup(self._sym_group)
        if check:
            if not is_cyclic:
                raise ValueError(str(self._sym_group) + ' is not a cyclic subgroup of the automorphism group of the graph.')
            if order != 2:
                raise ValueError('The order of ' + str(self._sym_group) + ' must be 2.')
        self._sym_gens = [gen]
        self.sigma =  gen
        self._vertex_orbits = None
        self._edge_orbits = None
        self._invariant_vertices = None
        self._invariant_edges = None
        self._NACs_computed = 'no'
        
        self._report('Vertex orbits: ' + str(self.vertex_orbits()), 2)
        if pos==None:
            pos_sym = False
            pos = {
                orbit[0]:self._pos[orbit[0]] for orbit in self.vertex_orbits()
                }
            for v in self._invariant_vertices:
                pos[v] = self._pos[v]
        if not pos_sym:
            self.set_symmetric_positions(pos)
            
    
    def invariant_vertices(self):
        if self._invariant_vertices != None:
            return self._invariant_vertices
        
        self._invariant_vertices = []
        
        for v in self.vertices(sort=False):
            if self.sigma(v)==v:
                self._invariant_vertices.append(v)
                
        return self._invariant_vertices
            
    def vertex_orbits(self):
        if self._vertex_orbits:
            return self._vertex_orbits
        
        verts = {v:1 for v in self.vertices(sort=False)}
        self._vertex_orbits = []
        for v in verts:
            if verts[v]:
                u = self.sigma(v)
                if u!=v:
                    verts[u] = 0
                    self._vertex_orbits.append([u,v])
        
        self._vertex_orbits += [[v] for v in self.invariant_vertices()]
        return self._vertex_orbits
            
    def edge_orbits(self):
        if self._edge_orbits:
            return self._edge_orbits
        
        edgs = {tuple(sorted(e)):1 for e in self.edges(labels=False, sort=False)}
        self._edge_orbits = []
        for e in edgs:
            e = tuple(sorted(e))
            if edgs[e]:
                f = tuple(sorted([self.sigma(e[0]),self.sigma(e[1])]))
                if e!=f:
                    edgs[f] = 0
                    self._edge_orbits.append([list(e),list(f)])
                else:
                    self._edge_orbits.append([list(e)])
        
        return self._edge_orbits
    
    def set_symmetric_positions(self, pos):
        for orbit in self.vertex_orbits():
            if len(orbit)==2:
                u,v = orbit
                if u in pos:
                    x, y = pos[u]
                    pos[v] = [-x,y]
                else:
                    x, y = pos[v]
                    pos[u] = [-x,y]
            else:
                pos[orbit[0]] = [0, pos[orbit[0]][1]]
        self.set_pos(pos)
        
    def invariant_edges(self):
        if self._invariant_edges != None:
            return self._invariant_edges
        
        self._invariant_edges = []
        for e in self.edges(labels=False, sort=False):
            u,v = e
            if self.sigma(u) in e and self.sigma(v) in e:
                self._invariant_edges.append(e)
        
        return self._invariant_edges
    
    def orthogonal_invariant_edges(self):
        return [e for e in self.invariant_edges() if self.sigma(e[0])==e[1]]
        
    def _find_NAC_colorings(self, onlyOne=False, names=False):
        r"""
        Find Cs-symmetric  of the graph and store them.

        The method finds NAC-colorings of the graph and store them in ``self._NAC_colorings``.
        The flag ``self._NACs_computed`` is changed to ``'yes'`` or ``'onlyOne'``.

        TODO:

         - skip testing combinations that fail on a subgraph 
        """   

        self._report('Searching NAC-colorings') 
        from .symmetric_NAC_coloring import PseudoRScoloring
        self._NAC_colorings = []
        inv_triangle_comps = []
        pairs = []
        for tr_comp in self.triangle_connected_components():
            c1 = Set([Set(e) for e in tr_comp])
            c2 = Set([Set([self.sigma(e[0]), self.sigma(e[1])]) for e in tr_comp])
            if c1 != c2:
                pairs.append(Set([c1, c2]))
            else:
                inv_triangle_comps += tr_comp
        pairs = list(Set(pairs))
        pairs = [[t1, t2] for t1,t2 in pairs]
        counter = 1
        if pairs:
            for comb in cartesian_product([[0,1]]+[[0,1,2] for _ in range(len(pairs)-1)]):
                try:
                    first2 = list(comb).index(2)  #this is to avoid conjugated NACs in the list
                    if not 1 in comb[:first2]:
                        continue
                except ValueError:
                    pass
                red = []
                blue = []
                gold = []
                for i,c in enumerate(comb):
                    if c==0:
                        gold += pairs[i][0]
                        gold += pairs[i][1]
                    elif c==1:
                        red += pairs[i][0]
                        blue += pairs[i][1]
                    else:
                        red += pairs[i][1]
                        blue += pairs[i][0]
                gold += inv_triangle_comps
                if names:
                    delta = PseudoRScoloring(self, [red, blue, gold], check=False, name='delta_' + str(counter))
                else:
                    delta = PseudoRScoloring(self, [red, blue, gold], check=False)
                if delta.is_pseudoRScoloring():
                    self._NAC_colorings.append(delta)
                    counter += 1
                    if onlyOne:
                        self._NACs_computed = 'onlyOne'
                        return
        self._NACs_computed = 'yes'
        
    def pseudoRScolorings(self, **kwargs):
        return self.NAC_colorings(**kwargs)
        
    def show_all_pseudoRScolorings(self, **kwargs):
        self.show_all_NAC_colorings(**kwargs)

    def Cs_closure(self, active_colorings=None, save_colorings=False):
        r"""
        Return the Cs-closure of the graph.
        """
        res = deepcopy(self)
        res._name = 'Cs-closure of ' + res.name()
        if active_colorings == None:
            active_colorings = self.NAC_colorings()
        
        def monochromatic_pairs(active):
            upairs = []
            for w in res.vertices(sort=False):
                for u,v in res.orthogonal_invariant_edges():
                    if not res.has_edge(w,v):
                        if w==res.sigma(w):
                            path = res.unicolor_path(w,v, active)
                            if path:
                                upairs.append([[w,v],path])
                        else:
                            path_u = res.unicolor_path(w,u, active)
                            path_v = res.unicolor_path(w,v, active)
                            if path_u and path_v:
                                if ([1 for delta in active if not delta.is_golden(path_u[0:2])] and 
                                    [1 for delta in active if not delta.is_golden(path_v[0:2])]):
                                    upairs.append([[w,v],path_v])
                                    upairs.append([[w,u],path_u])
            return upairs
        
        from .symmetric_NAC_coloring import PseudoRScoloring
        upairs = monochromatic_pairs(active_colorings)
        while upairs:
            res.add_edges([e for e,_ in upairs])
            res.add_edges([[self.sigma(e[0]), self.sigma(e[1])] for e,_ in upairs])
            active_res = []
            for col in active_colorings:
                red = col.red_edges()
                blue = col.blue_edges()
                golden = col.golden_edges()
                for e, path in upairs:
                    sigma_e = [self.sigma(e[0]), self.sigma(e[1])]
                    if col.is_red(path[0:2]):
                        red.append(e)
                        blue.append(sigma_e)
                    elif col.is_golden(path[0:2]):
                        golden.append(e)
                    else:
                        blue.append(e)
                        red.append(sigma_e)
                if col._name:
                    col_new = PseudoRScoloring(res, [red, blue, golden], check=False, name=col._name)
                else:
                    col_new = PseudoRScoloring(res, [red, blue, golden], check=False)
                if col_new.is_pseudoRScoloring():
                    active_res.append(col_new)
            active_colorings = active_res
            upairs = monochromatic_pairs(active_colorings)
        if save_colorings:
            res._NAC_colorings = active_colorings
            res._NACs_computed = True
        return res

    @staticmethod
    def Cs_symmetries_gens(graph):
        r"""
        Return the list of generators of Cs symmetries of the graph.
        """
        return [sigma for sigma in SymmetricFlexRiGraph._cyclic_subgroups(graph.automorphism_group(), 2)]
    
    @staticmethod    
    def Cs_symmetries_gens_according_isomorphic_orbits(G):
        r"""
        Return the generators of Cs-symmetries divided according to isomorphic orbits.
        
        OUTPUT:
        
        The output is the list of lists of generators - two generators are in the same
        list if there is a graph isomorphism mapping orbits of one generator to orbits of the other.
        """
        def gen2orbit_sets(gamma):
            Gsym = CsSymmetricFlexRiGraph(G, gamma)
            return Set([Set(orbit) for orbit in Gsym.vertex_orbits()])
        
        def orbits_image(tau, orbits):
            return Set([Set([tau(v) for v in orbit]) for orbit in orbits])
        
        autG = G.automorphism_group()
        symmetries = CsSymmetricFlexRiGraph.Cs_symmetries_gens(G)
        if symmetries==[]:
            return []
        res = {}
        for omega in symmetries:
            orbits = gen2orbit_sets(omega)
            for tau in autG:
                tau_orbits = orbits_image(tau, orbits)
                if tau_orbits in res:
                    res[tau_orbits].append(omega)
                    break
            else:
                res[tau_orbits] = [omega]
        return list(res.values())    
__doc__ = __doc__.replace(
    "{INDEX_OF_METHODS_SYMMETRIC_FLEXRIGRAPH}", gen_thematic_rest_table_index(SymmetricFlexRiGraph))


__doc__ = __doc__.replace(
    "{INDEX_OF_METHODS_CN_SYMMETRIC_FLEXRIGRAPH}", gen_thematic_rest_table_index(CnSymmetricFlexRiGraph))


__doc__ = __doc__.replace(
    "{INDEX_OF_METHODS_CS_SYMMETRIC_FLEXRIGRAPH}", gen_thematic_rest_table_index(CsSymmetricFlexRiGraph))
















