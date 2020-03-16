# -*- coding: utf-8 -*-
r"""
This module implements functionality for investigating rigidity and flexibility of graphs with a symmetry.

Methods
-------

**SymmetricFlexRiGraph**

{INDEX_OF_METHODS_SYMMETRIC_FLEXRIGRAPH}

**CnSymmetricFlexRiGraph**

{INDEX_OF_METHODS_CN_SYMMETRIC_FLEXRIGRAPH}

AUTHORS:

-  Jan Legerský (2020-03-12): initial version

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
from sage.all import pi, cos, sin
import random
from itertools import chain

from sage.misc.rest_index_of_methods import doc_index, gen_thematic_rest_table_index
from sage.rings.integer import Integer


from .NAC_coloring import NACcoloring
from .flexible_rigid_graph import FlexRiGraph

    
    
class SymmetricFlexRiGraph(FlexRiGraph):
    r"""
    The class SymmetricFlexRiGraph is inherited from :class:`FlexRiGraph`.
    It represents a graph with a given symmetry.

    INPUT:

    - ``data``: provides the information about edges, see :class:`FlexRiGraph`..

    - ``symmetry`` -- `sage.graphs.graph.Graph <http://doc.sagemath.org/html/en/reference/groups/sage/groups/perm_gps/permgroup.html>`_
      that is a subgroup of the automorphism group of the graph or the list of its generators 

    TODO:
    
        examples
    """

    def __init__(self, data, symmetry, pos=None, name=None, check=True):
        super(SymmetricFlexRiGraph, self).__init__(data, pos, name, check)
        if isinstance(symmetry, PermutationGroup_generic):
            self._sym_group = symmetry
            self._sym_gens = self._sym_group.gens()
        elif isinstance(symmetry, list):
            self._sym_gens = symmetry
            self._sym_group = PermutationGroup(symmetry, domain=self.vertices())
        
        for gen in self._sym_gens:
            for u,v in self.edges(labels=False):
                if not self.has_edge(gen(u), gen(v)):
                    raise ValueError('`symmetry must be a subgroup of the automorphism group of the graph or the list of its generators, not '
                                     + str(self._sym_group))                    


    def _repr_(self):
        return super(SymmetricFlexRiGraph, self)._repr_() + '\nwith the symmetry ' + str(self._sym_group)


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
        - input only generator
    """
    def __init__(self, data, symmetry, pos=None, name=None, check=True):
        super(CnSymmetricFlexRiGraph, self).__init__(data, symmetry, pos, name, check)
        is_cyclic, gen, order = CnSymmetricFlexRiGraph.is_cyclic_subgroup(self._sym_group)
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
        
        if pos==None:
            pos = {
                orbit[0]:self._pos[orbit[0]] for orbit in self.vertex_orbits()
                }
        self.set_symmetric_positions(pos)
         
    def vertex_orbits(self):
        r"""
        Return the orbits of vertices.
        """
        if self._vertex_orbits:
            return self._vertex_orbits
        
        self._vertex_orbits = []
        verts = {v:0 for v in self.vertices()}
        for v in self.invariant_vertices():
            verts.pop(v)
        while verts:
            v, _ = verts.popitem()
            orbit = [v]
            for _ in range(1,self.n):
                w = self.omega(orbit[-1])
                orbit.append(w)
                verts.pop(w)
            self._vertex_orbits.append(orbit)
                
        self._vertex_orbits += self.invariant_vertices()

        return self._vertex_orbits
    
           
    def edge_orbits(self):
        r"""
        Return the orbits of edges.
        """
        if self._edge_orbits:
            return self._edge_orbits
        orbits = []
        for u,v in self.edges(labels=False):
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
        self._invariant_vertices = [v for v in self.vertices() if len(self.omega.orbit(v))<self.n]
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
        from .symmetric_NAC_coloring import CnSymmetricNACcoloring
        FlexRiGraph._find_NAC_colorings(self, onlyOne=onlyOne, names=names)
        symmetric_NACs = []
        for delta in self._NAC_colorings:
            delta_sym = CnSymmetricNACcoloring(self, delta, check=False)
            if delta_sym.is_Cn_symmetric():
                symmetric_NACs.append(delta_sym)
        self._NAC_colorings = symmetric_NACs
    
    
    @doc_index("NAC-colorings")   
    def NAC_colorings(self):
        r"""
        Return $\\mathcal{C}_n$-symmetric NAC-colorings.
        """       
        if self._NACs_computed != 'yes':
            self._find_NAC_colorings()
        return self._NAC_colorings

    
    
    @staticmethod
    def is_Cn_symmetry(graph, sigma, n):
        r"""
        Return whether ``sigma`` generates a $\\mathcal{C}_n$-symmetry of the `graph`.
        """
        partially_inv = [v for v in graph.vertices() if len(sigma.orbit(v))<n]
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
        """
        
        res = []
        for sigma in CnSymmetricFlexRiGraph.cyclic_subgroups(graph.automorphism_group(), n):
            if CnSymmetricFlexRiGraph.is_Cn_symmetry(graph, sigma, n):
                res.append(sigma)
        return res

    def _edges_with_same_color(self):
        V = [tuple(sorted(e)) for e in self.edges(labels=False)]
        E = []
        for tr_comp in self.triangle_connected_components():
            E += [[tuple(sorted(e)), tuple(sorted(f))] for e, f in zip(tr_comp[:-1], tr_comp[1:])]
        for orbit in self.edge_orbits():
            E += [[tuple(sorted(e)), tuple(sorted(f))] for e, f in zip(orbit[:-1], orbit[1:])]
        return [[[u,v] for u, v in comp] for comp in Graph([V, E], format='vertices_and_edges').connected_components()]

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
    def cyclic_subgroups(group, order):
        r'''
        Return all cyclic subgroups of ``group`` with given ``order``.
        '''
        res_sbgrps = []
        for sbgrp in group.subgroups():
            cyclic, gen, n = CnSymmetricFlexRiGraph.is_cyclic_subgroup(sbgrp)
            if cyclic and n == order:
                res_sbgrps.append(gen)
        return res_sbgrps

   

__doc__ = __doc__.replace(
    "{INDEX_OF_METHODS_SYMMETRIC_FLEXRIGRAPH}", gen_thematic_rest_table_index(SymmetricFlexRiGraph))


__doc__ = __doc__.replace(
    "{INDEX_OF_METHODS_CN_SYMMETRIC_FLEXRIGRAPH}", gen_thematic_rest_table_index(CnSymmetricFlexRiGraph))


















