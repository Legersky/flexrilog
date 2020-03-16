# -*- coding: utf-8 -*-
r"""
This module implements the functionality for determining possible motions of a graph.

Methods
-------

{INDEX_OF_METHODS}


AUTHORS:

-  Jan Legerský (2019-02-18): initial version
-  Jan Legerský (2020-03-12): update to SageMath 9.0

MotionClassifier
----------------
"""


from sage.misc.rest_index_of_methods import doc_index, gen_thematic_rest_table_index
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

from sage.all import Graph, Set, Subsets, deepcopy#,, find_root ceil, sqrt, matrix, copy,
from sage.all import SageObject, PolynomialRing, QQ, flatten, ideal, sgn
from sage.all import table, show, factor, latex
#from sage.all import vector, matrix, sin, cos, pi,  var,  RR,  floor,  tan
#from sage.all import FunctionField, QQ,  sqrt,  function
from sage.misc.rest_index_of_methods import gen_rest_table_index
from sage.rings.integer import Integer
_sage_const_3 = Integer(3); _sage_const_2 = Integer(2); _sage_const_1 = Integer(1);
#_sage_const_0 = Integer(0); _sage_const_6 = Integer(6); _sage_const_5 = Integer(5);
#_sage_const_4 = Integer(4); _sage_const_13 = Integer(13); _sage_const_12 = Integer(12)
#from sage.rings.rational import Rational
from .flexible_rigid_graph import FlexRiGraph
from collections import Counter
from IPython.core.display import display

class MotionClassifier(SageObject):
    r"""
    This class implements the functionality for determining possible motions of a graph.
    """
    def __init__(self, graph, four_cycles=[], separator='', edges_ordered=[]):
        if not (isinstance(graph, FlexRiGraph) or 'FlexRiGraph' in str(type(graph))):
            raise TypeError('The graph must be of the type FlexRiGraph.')
        self._graph = graph

        if four_cycles == []:
            self._four_cycles = self._graph.four_cycles(only_with_NAC=True) 
        else:
            self._four_cycles = four_cycles

        if not self._graph.are_NAC_colorings_named():
            self._graph.set_NAC_colorings_names()

#        -----Polynomial Ring for leading coefficients-----
        ws = []
        zs = []
        lambdas = []
        ws_latex = []
        zs_latex = []
        lambdas_latex = []
        
        if edges_ordered==[]:
            edges_ordered = self._graph.edges(labels=False)
        else:
            if (Set([self._edge2str(e) for e in edges_ordered]) !=
                Set([self._edge2str(e) for e in self._graph.edges(labels=False)])):
                raise ValueError('The provided ordered edges do not match the edges of the graph.')

        for e in edges_ordered:
            ws.append('w' + self._edge2str(e))
            zs.append('z' + self._edge2str(e))
            lambdas.append('lambda' + self._edge2str(e))
            ws_latex.append('w_{' + self._edge2str(e).replace('_', separator) + '}')
            zs_latex.append('z_{' + self._edge2str(e).replace('_', separator) + '}')
            lambdas_latex.append('\\lambda_{' + self._edge2str(e).replace('_', separator) + '}')

        self._ringLC = PolynomialRing(QQ, names=lambdas+ws+zs) #, order='lex')
        self._ringLC._latex_names = lambdas_latex + ws_latex + zs_latex
        self._ringLC_gens = self._ringLC.gens_dict()

        self._ring_lambdas = PolynomialRing(QQ, names=lambdas + ['u'])
        self._ring_lambdas._latex_names = lambdas_latex + ['u']
        self._ring_lambdas_gens = self._ring_lambdas.gens_dict()
        self.aux_var = self._ring_lambdas_gens['u']
        
        xs = []
        ys = []
        xs_latex = []
        ys_latex = []
        for v in self._graph.vertices():
            xs.append('x' + str(v))
            ys.append('y' + str(v))
            xs_latex.append('x_{' + str(v) + '}')
            ys_latex.append('y_{' + str(v) + '}')
            
        self._ring_coordinates = PolynomialRing(QQ, names=lambdas+xs+ys)
        self._ring_coordinates._latex_names = lambdas_latex + xs_latex + ys_latex
        self._ring_coordinates_gens = self._ring_coordinates.gens_dict()
        
        
#        ----Ramification-----
#         if len(self._graph.NAC_colorings()) > 1: 
        self._ring_ramification = PolynomialRing(QQ,
                                                 [col.name() for col in self._graph.NAC_colorings()],
                                                 len(self._graph.NAC_colorings()))
#         else:
#             self._ring_ramification = PolynomialRing(QQ, self._graph.NAC_colorings()[0].name())
        self._ring_ramification_gens = self._ring_ramification.gens_dict()
        self._restriction_NAC_types = self.NAC_coloring_restrictions()

#        -----Graph of 4-cycles-----
        self._four_cycle_graph = Graph([self._four_cycles,[]], format='vertices_and_edges')

        for c1, c2 in Subsets(self._four_cycle_graph.vertices(), 2):
            intersection = self.cycle_edges(c1, sets=True).intersection(self.cycle_edges(c2, sets=True))
            if len(intersection)>=2 and len(intersection[0].intersection(intersection[1]))==1:
                common_vert = intersection[0].intersection(intersection[1])[0]
                self._four_cycle_graph.add_edge(c1, c2, common_vert)

#        -----Cycle with orthogonal diagonals due to NAC-----
        self._orthogonal_diagonals = {
                delta.name(): [cycle for cycle in self._four_cycle_graph if delta.cycle_has_orthogonal_diagonals(cycle)]
                for delta in self._graph.NAC_colorings()}

    @doc_index("Constraints on edge lengths")
    def four_cycles_ordered(self):
        r"""
        Heuristic order of 4-cycles.
        """
        cliques = self._four_cycle_graph.cliques_maximal()
        cycles = max(cliques,
                     key=lambda clique: sum([self._four_cycle_graph.degree(v) for v in clique]))
        missing_cliques = {tuple(clique):0 for clique in cliques}
        missing_cliques.pop(tuple(cycles))
        while missing_cliques:
            next_clique = max(missing_cliques.keys(),
                             key=lambda clique:sum([1 for c in clique for c2 in self._four_cycle_graph.neighbors(c) if c2 in cycles]))
            missing_cliques.pop(next_clique)
            missing_cycles = {c:0 for c in next_clique if not c in cycles}
            while missing_cycles:
                next_cycle = max(missing_cycles.keys(),
                                key=lambda c:sum([1 for c2 in self._four_cycle_graph.neighbors(c) if c2 in cycles]))
                cycles.append(next_cycle)
                missing_cycles.pop(next_cycle)

        missing_cycles = {c:0 for c in self._four_cycle_graph.vertices() if not c in cycles}
        while missing_cycles:
            next_cycle = max(missing_cycles.keys(),
                            key=lambda c:sum([1 for c2 in self._four_cycle_graph.neighbors(c) if c2 in cycles]))
            cycles.append(next_cycle)
            missing_cycles.pop(next_cycle)
        return cycles

    def _repr_(self):
        return 'Motion Classifier of ' + str(self._graph)

    @staticmethod
    def _edge2str(e):
        if e[0]<e[1]:
            return str(e[0]) + '_' + str(e[1])
        else:
            return str(e[1]) + '_' + str(e[0])

    
    @staticmethod
    @doc_index("Other")
    def cycle_edges(cycle, sets=False):
        r"""
        Return edges of a 4-cycle.
        """
        if sets:
            return Set([Set(list(e)) for e in zip(cycle, list(cycle[1:])+[cycle[0]])])
        else:
            return [list(e) for e in zip(cycle, list(cycle[1:])+[cycle[0]])]

    @staticmethod
    @doc_index("Other")
    def four_cycle_normal_form(cycle, motion_type):
        r"""
        Return a 4-cycle with a motion type in the normal form.
        """
        i = cycle.index(min(cycle))
        oe =  ['o', 'e']
        if i % 2 == 1 and motion_type in oe:
            motion_type = oe[1 - oe.index(motion_type)]
        tmp_c = cycle[i:]+cycle[:i]
        if tmp_c[1]<tmp_c[3]:
            return tmp_c,  motion_type
        else:
            return (tmp_c[0], tmp_c[3], tmp_c[2], tmp_c[1]), motion_type

    @staticmethod
    @doc_index("Other")
    def normalized_motion_types(motion_types):
        r"""
        Return motion types in the normal form.
        """
        res = {}
        for c, t in motion_types.items():
            norm_c, norm_t = MotionClassifier.four_cycle_normal_form(c, t)
            res[norm_c] = norm_t
        return res

    def _w(self, e):
        if e[0] < e[1]:
            return self._ringLC_gens['w'+self._edge2str(e)]
        else:
            return -self._ringLC_gens['w'+self._edge2str(e)]

    def _z(self, e):
        if e[0] < e[1]:
            return self._ringLC_gens['z'+self._edge2str(e)]
        else:
            return -self._ringLC_gens['z'+self._edge2str(e)]

    def _lam(self, e):
        return self._ringLC_gens['lambda'+self._edge2str(e)]
    
    @doc_index("Constraints on edge lengths")
    def lam(self, u,v):
        r"""
        Return the variable for edge length in the ring of edge lengths.
        """
        return self._ring_lambdas_gens['lambda'+self._edge2str([u,v])]

    @doc_index("Motion types consistent with 4-cycles")
    def mu(self, delta):
        r"""
        Return the variable for a given NAC-coloring.
        """
        if type(delta)==str:
            return self._ring_ramification_gens[delta]
        else:
            return self._ring_ramification_gens[delta.name()]

    @doc_index("System of equations for coordinates")
    def x(self, v):
        r"""
        Return the variable for x coordinate of a vertex. 
        """
        return self._ring_coordinates_gens['x'+str(v)]

    @doc_index("System of equations for coordinates")
    def y(self, v):
        r"""
        Return the variable for y coordinate of a vertex. 
        """
        return self._ring_coordinates_gens['y'+str(v)]

    @doc_index("System of equations for coordinates")
    def l(self, u,v):
        r"""
        Return the variable for edge length in the ring with coordinates.
        """
        return self._ring_coordinates_gens['lambda'+self._edge2str([u,v])]

    @doc_index("Constraints on edge lengths")
    def equations_from_leading_coefs(self, delta, extra_eqs=[], check=True):
        r"""
        Return equations for edge lengths from leading coefficients system.

        EXAMPLES::

            sage: from flexrilog import GraphGenerator, MotionClassifier
            sage: K33 = GraphGenerator.K33Graph()
            sage: M = MotionClassifier(K33)
            sage: M.equations_from_leading_coefs('epsilon56')
            [lambda1_2^2 - lambda1_4^2 - lambda2_3^2 + lambda3_4^2]

        ::

            sage: M.equations_from_leading_coefs('omega1')
            Traceback (most recent call last):
            ...
            ValueError: The NAC-coloring must be a singleton.

        ::

            sage: M.equations_from_leading_coefs('omega1', check=False)
            [lambda2_5^2*lambda3_4^2 - lambda2_5^2*lambda3_6^2 - lambda2_3^2*lambda4_5^2 + lambda3_6^2*lambda4_5^2 + lambda2_3^2*lambda5_6^2 - lambda3_4^2*lambda5_6^2]
        """

        if type(delta) == str:
            delta = self._graph.name2NAC_coloring(delta)

        if check:
            if not delta.is_singleton():
                raise ValueError('The NAC-coloring must be a singleton.')
        eqs_lengths=[]
        for e in self._graph.edges():
            eqs_lengths.append(self._z(e)*self._w(e) - self._lam(e)**_sage_const_2)


        eqs_w=[]
        eqs_z=[]
        for T in self._graph.spanning_trees():
            for e in self._graph.edges():
                eqw = 0
                eqw_all = 0
                eqz = 0
                eqz_all = 0
                path = T.shortest_path(e[0],e[1])
                for u,v in zip(path, path[1:]+[path[0]]):
                    if delta.is_red(u,v):
                        eqz+=self._z([u,v])
                    else:
                        eqw+=self._w([u,v])
                    eqw_all+=self._w([u,v])
                    eqz_all+=self._z([u,v])
                if eqw:
                    eqs_w.append(eqw)
                else:
                    eqs_w.append(eqw_all)
                if eqz:
                    eqs_z.append(eqz)
                else:
                    eqs_z.append(eqz_all)

        equations = (ideal(eqs_w).groebner_basis()
                     + ideal(eqs_z).groebner_basis()
                     + eqs_lengths
                     + [self._ringLC(eq) for eq in extra_eqs])
        return [self._ring_lambdas(eq)
                for eq in ideal(equations).elimination_ideal(flatten(
                    [[self._w(e), self._z(e)] for e in self._graph.edges()])).basis
                ]

    @staticmethod
    def _pair_ordered(u,v):
        if u<v:
            return (u, v)
        else:
            return (v, u)

    @staticmethod
    def _edge_ordered(u,v):
        return MotionClassifier._pair_ordered(u, v)

#    @staticmethod
    def _set_two_edge_same_lengths(self, H, u, v, w, y, k):
        if H[self._edge_ordered(u,v)]==None and H[self._edge_ordered(w,y)]==None:
            H[self._edge_ordered(u,v)] = k
            H[self._edge_ordered(w,y)] = k
            return 1
        elif H[self._edge_ordered(u,v)]==None:
            H[self._edge_ordered(u,v)] = H[self._edge_ordered(w,y)]
            return 0
        elif H[self._edge_ordered(w,y)]==None:
            H[self._edge_ordered(w,y)] = H[self._edge_ordered(u,v)]
            return 0
        elif H[self._edge_ordered(u,v)]!=H[self._edge_ordered(w,y)]:
            col= H[self._edge_ordered(u,v)]
            for u,v in H.keys():
                if H[(u,v)]==col:
                    H[(u,v)] = H[self._edge_ordered(w,y)]
            return 0
        return 0

    def _set_same_lengths(self, H, types):
        for u,v in H.keys():
            H[(u,v)] = None
        k=1
        for c in types:
            motion = types[c]
            if motion=='a' or motion=='p':
                k += self._set_two_edge_same_lengths(H, c[0], c[1], c[2], c[3], k)
                k += self._set_two_edge_same_lengths(H, c[1], c[2], c[0], c[3], k)
            elif motion=='o':
                k += self._set_two_edge_same_lengths(H, c[0], c[1], c[1], c[2], k)
                k += self._set_two_edge_same_lengths(H, c[2], c[3], c[0], c[3], k)
            elif motion=='e':
                k += self._set_two_edge_same_lengths(H, c[1], c[2], c[2], c[3], k)
                k += self._set_two_edge_same_lengths(H, c[0], c[1], c[0], c[3], k)

    @doc_index("Constraints on edge lengths")
    def motion_types2same_edge_lenghts(self, motion_types):
        r"""
        Return the dictionary of same edge lengths enforced by given motion types.
        """
        H = {self._edge_ordered(u,v):None for u,v in self._graph.edges(labels=False)}
        self._set_same_lengths(H, motion_types)
        return H

    @doc_index("Motion types consistent with 4-cycles")
    def NAC_coloring_restrictions(self):
        r"""
        Return types of restrictions of NAC-colorings to 4-cycles.

        EXAMPLE::

            sage: from flexrilog import MotionClassifier, GraphGenerator
            sage: MC = MotionClassifier(GraphGenerator.K33Graph())
            sage: MC.NAC_coloring_restrictions()
            {(1, 2, 3, 4): {'L': ['omega3', 'omega1', 'epsilon36', 'epsilon16'],
              'O': ['epsilon34', 'epsilon14', 'epsilon23', 'epsilon12'],
              'R': ['omega4', 'epsilon45', 'omega2', 'epsilon25']},
            ...
             (3, 4, 5, 6): {'L': ['omega5', 'omega3', 'epsilon25', 'epsilon23'],
              'O': ['epsilon56', 'epsilon36', 'epsilon45', 'epsilon34'],
              'R': ['omega6', 'epsilon16', 'omega4', 'epsilon14']}}
        """
        res = {cycle:{'O':[], 'L':[], 'R':[]} for cycle in self._four_cycles}
        for delta in self._graph.NAC_colorings():
            for cycle in self._four_cycles:
                colors = [delta.color(e) for e in self.cycle_edges(cycle)]
                if colors[0]==colors[1]:
                    if colors[0]!=colors[2]:
                        res[cycle]['R'].append(delta.name())
                elif colors[1]==colors[2]:
                    res[cycle]['L'].append(delta.name())
                else:
                    res[cycle]['O'].append(delta.name())
        return res

    @doc_index("Motion types consistent with 4-cycles")
    def ramification_formula(self, cycle, motion_type):
        r"""
        Return ramification formula for a given 4-cycle and motion type.

        EXAMPLES::

            sage: from flexrilog import MotionClassifier, GraphGenerator
            sage: MC = MotionClassifier(GraphGenerator.K33Graph())
            sage: MC.ramification_formula((1,2,3,4), 'a')
            [epsilon34,
             epsilon14,
             epsilon23,
             epsilon12,
             omega3 + omega1 + epsilon36 + epsilon16 - omega4 - epsilon45 - omega2 - epsilon25]
        """
        eqs_present = []
        eqs_zeros = []
        NAC_types = self.motion_types2NAC_types(motion_type)
        for t in ['L','O','R']:
            if t in NAC_types:
                eqs_present.append(sum([self.mu(delta) for delta in self._restriction_NAC_types[cycle][t]]))
            else:
                eqs_zeros += [self.mu(delta) for delta in self._restriction_NAC_types[cycle][t]]
        
        if 0 in eqs_present:
            return [self.mu(delta) for delta in self._graph.NAC_colorings()]
        if len(eqs_present)==2:
            return eqs_zeros + [eqs_present[0] - eqs_present[1]]
        elif len(eqs_present)==3:
            return eqs_zeros + [eqs_present[0] - eqs_present[1], eqs_present[1] - eqs_present[2]]
        else:
            return eqs_zeros

    @staticmethod
    @doc_index("Other")
    def motion_types2NAC_types(m):
        r"""
        Return NAC-coloring types for a given motion type.
        """
        if m=='g':
            return ['L','R','O']
        if m=='a':
            return ['L','R']
        if m=='p':
            return ['O']
        if m=='e':
            return ['R','O']
        if m=='o':
            return ['L','O']

    @staticmethod
    @doc_index("Other")
    def NAC_types2motion_type(t):
        r"""
        Return the motion type for given types of NAC-colorings.
        """
        if Set(t)==Set(['L','R','O']):
            return 'g'
        if Set(t)==Set(['L','R']):
            return 'a'
        if Set(t)==Set(['O']):
            return 'p'
        if Set(t)==Set(['R','O']):
            return 'e'
        if Set(t)==Set(['L','O']):
            return 'o'
    
    @doc_index("Other")
    def active_NACs2motion_types(self, active):
        r"""
        Return the motion types of 4-cycles for a given set of active NAC-colorings. 
        """
        motion_types = {cycle:[] for cycle in self._four_cycles}
        for delta in active:
            if type(delta)!=str:
                delta = delta.name()
            for cycle in motion_types:
                motion_types[cycle] += [t for t, colorings 
                                        in self._restriction_NAC_types[cycle].items()
                                        if delta in colorings]
        for cycle in motion_types:
            motion_types[cycle] = self.NAC_types2motion_type(motion_types[cycle])
        return motion_types

    @staticmethod
    def _same_edge_lengths(K, edges_to_check):
        if edges_to_check:
            length = K[MotionClassifier._edge_ordered(edges_to_check[0][0], edges_to_check[0][1])]
            if length==None:
                return False
            for u,v in edges_to_check:
                if length!=K[MotionClassifier._edge_ordered(u,v)]:
                    return False
            return True
        else:
            return True

    @doc_index("Motion types consistent with 4-cycles")
    def consequences_of_nonnegative_solution_assumption(self, eqs):
        r"""
        Return equations implied by the assumption of the existence of nonnegative solutions.
        """
        n_zeros_prev = -1
        zeros = []
        gb = eqs
        while n_zeros_prev!=len(zeros):
            n_zeros_prev = len(zeros)
            gb = self._ring_ramification.ideal(gb + zeros).groebner_basis()
#             gb = self._ring_ramification.ideal(gb + zeros).groebner_basis()
            zeros = []
            for eq in gb:
                coefs = eq.coefficients()
                if sum([sgn(a)*sgn(b) for a,b in zip(coefs[:-1],coefs[1:])])==len(coefs)-1:
                    zeros += eq.variables()
        return [zeros, gb]

#    @staticmethod
#    def consequences_of_nonnegative_solution_assumption(eqs):
#        n_zeros_prev = -1
#        zeros = {}
#        gb = ideal(eqs).groebner_basis()
#        while n_zeros_prev!=len(zeros):
#            n_zeros_prev = len(zeros)
#            gb = [eq.substitute(zeros) for eq in gb if eq.substitute(zeros)!=0]
#            for eq in gb:
#                coefs = eq.coefficients()
#                if sum([sgn(a)*sgn(b) for a,b in zip(coefs[:-1],coefs[1:])])==len(coefs)-1:
#                    for zero_var in eq.variables():
#                        zeros[zero_var] = 0
#        return [zeros.keys(), gb]

    @doc_index("Motion types consistent with 4-cycles")
    def consistent_motion_types(self):#, cycles=[]):
        r"""
        Return the list of motion types consistent with 4-cycles.
        """
#         if cycles==[]:
        cycles = self.four_cycles_ordered()

        k23s = [Graph(self._graph).subgraph(k23_ver).edges(labels=False) for k23_ver in self._graph.induced_K23s()]

        aa_pp = [('a', 'a'), ('p', 'p')]
        ao = [('a','o'), ('o','a')]
        ae = [('a','e'), ('e','a')]
        oe = [('o', 'e'), ('e', 'o')]
        oo_ee = [('e','e'), ('o','o')]

        H = {self._edge_ordered(u,v):None for u,v in self._graph.edges(labels=False)}
        types_prev=[[{}, []]]
        
        self._num_tested_combinations = 0

        for i, new_cycle in enumerate(cycles):
            types_ext = []
            new_cycle_neighbors = [[c2,
                                    new_cycle.index(self._four_cycle_graph.edge_label(new_cycle, c2)),
                                    c2.index(self._four_cycle_graph.edge_label(new_cycle, c2)),
                                   ] for c2 in self._four_cycle_graph.neighbors(new_cycle) if c2 in cycles[:i]]
            for types_original, ramification_eqs_prev in types_prev:
                for type_new_cycle in ['g','a','p','o','e']:
                    self._num_tested_combinations +=1
                    types = deepcopy(types_original)
                    types[tuple(new_cycle)] = type_new_cycle
    #                 H = deepcopy(orig_graph)
                    inconsistent = False

                    for c2, new_index, c2_index in new_cycle_neighbors:
                        type_pair = (types[new_cycle], types[c2])
                        if (type_pair in aa_pp
                                or (type_pair in oe and new_index%2 == c2_index%2)
                                or (type_pair in oo_ee and new_index%2 != c2_index%2)):
                            inconsistent = True
                            break
                        if type_pair in ao:
                            ind_o = type_pair.index('o')
                            if [new_index, c2_index][ind_o] % 2 == 1:
                            # odd deltoid (1,2,3,4) is consistent with 'a' if the common vertex is odd,
                            # but Python lists are indexed from 0
                                inconsistent = True
                                break
                        if type_pair in ae:
                            ind_e = type_pair.index('e')
                            if [new_index, c2_index][ind_e] % 2 == 0:
                                inconsistent = True
                                break
                    if inconsistent:
                        continue

                    self._set_same_lengths(H, types)
                    for c in types:
                        if types[c]=='g':
                            labels = [H[self._edge_ordered(c[i-1],c[i])] for i in range(0,4)]
                            if (not None in labels
                                and ((len(Set(labels))==2 and labels.count(labels[0])==2)
                                    or len(Set(labels))==1)):
                                inconsistent = True
                                break
                    if inconsistent:
                        continue
                    for K23_edges in k23s:
                        if MotionClassifier._same_edge_lengths(H, K23_edges):
                            inconsistent = True
                            break
                    if inconsistent:
                        continue

                    ramification_eqs = ramification_eqs_prev + self.ramification_formula(new_cycle, type_new_cycle)
                    zero_variables, ramification_eqs = self.consequences_of_nonnegative_solution_assumption(ramification_eqs)
                    for cycle in types:
                        if inconsistent:
                            break
                        for t in self.motion_types2NAC_types(types[cycle]):
                            has_necessary_NAC_type = False
                            for delta in self._restriction_NAC_types[cycle][t]:
                                if not self.mu(delta) in zero_variables:
                                    has_necessary_NAC_type = True
                                    break
                            if not has_necessary_NAC_type:
                                inconsistent = True
                                break
                    if inconsistent:
                        continue

                    types_ext.append([types, ramification_eqs])

            types_prev=types_ext

        return [t for t, _ in types_prev]

    @doc_index("Other")
    def active_NAC_coloring_names(self, motion_types):
        r"""
        Return the names of active NAC-colorings for given motion types.
        """
        return [delta.name() for delta in self.motion_types2active_NACs(motion_types)]
        
    @doc_index("Motion types consistent with 4-cycles")
    def motion_types2active_NACs(self, motion_types):
        r"""
        Return the active NAC-colorings for given motion types, if uniquely determined.
        """
        zeros, eqs = self.consequences_of_nonnegative_solution_assumption(
            flatten([self.ramification_formula(c, motion_types[c]) for c in motion_types]))

        if self._ring_ramification.ideal(eqs).dimension()==1:
            return [delta for delta in self._graph.NAC_colorings() if not self.mu(delta) in zeros]
        else:
            raise NotImplementedError('There might be more solutions (dim '+str(
                self._ring_ramification.ideal(eqs).dimension()) + ')')

    @doc_index("General methods")
    def motion_types_equivalent_classes(self,  motion_types_list):
        r"""
        Split a list of motion types into isomorphism classes.
        """
        aut_group = self._graph.automorphism_group()
        classes = [
            [( motion_types_list[0],
              self.normalized_motion_types( motion_types_list[0]),
              Counter([('d' if t in ['e','o'] else t) for c, t in  motion_types_list[0].items()]))]
        ]
        for next_motion in  motion_types_list[1:]:
            added = False
            next_sign = Counter([('d' if t in ['e','o'] else t) for c, t in next_motion.items()])
            for cls in classes:
                repr_motion_types = cls[0][1]
                if cls[0][2]!=next_sign:
                    continue
                for sigma in aut_group:
                    next_motion_image = self.normalized_motion_types({tuple(sigma(v) for v in c): t
                                                        for c,t in next_motion.items()})
                    for c in repr_motion_types:
                        if repr_motion_types[c]!=next_motion_image[c]:
                            break
                    else:
                        cls.append([next_motion])
                        added = True
                        break
#                    if not False in [repr_motion_types[c]==next_motion_image[c] for c in repr_motion_types]:
#                        cls.append(next_motion)
#                        added = True
#                        break
                if added:
                    break
            else:
                classes.append([(next_motion, self.normalized_motion_types(next_motion), next_sign)])
        return [[t[0] for t in cls] for cls in classes]

    @doc_index("General methods")
    def check_orthogonal_diagonals(self, motion_types,  active_NACs, extra_cycles_orthog_diag=[]):
        r"""
        Check the necessary conditions for orthogonal diagonals.

        TODO:
        
        return orthogonality_graph
        """
        perp_by_NAC = [cycle for delta in active_NACs for cycle in self._orthogonal_diagonals[delta]]
        deltoids = [cycle for cycle, t in motion_types.items() if t in ['e','o']]

        orthogonalLines = []
        for perpCycle in perp_by_NAC + deltoids + extra_cycles_orthog_diag:
            orthogonalLines.append(Set([Set([perpCycle[0],perpCycle[2]]), Set([perpCycle[1],perpCycle[3]])]))

        orthogonalityGraph = Graph(orthogonalLines, format='list_of_edges', multiedges=False)
        n_edges = -1

        while  n_edges != orthogonalityGraph.num_edges():
            n_edges = orthogonalityGraph.num_edges()
            for perp_subgraph in orthogonalityGraph.connected_components_subgraphs():
                isBipartite, partition = perp_subgraph.is_bipartite(certificate=True)
                if isBipartite:
                    graph_0 = Graph([v.list() for v in partition if partition[v]==0])
                    graph_1 = Graph([v.list() for v in partition if partition[v]==1])
                    for comp_0 in graph_0.connected_components():
                        for comp_1 in graph_1.connected_components():
                            for e0 in Subsets(comp_0,2):
                                for e1 in Subsets(comp_1,2):
                                    orthogonalityGraph.add_edge([Set(e0), Set(e1)])
                else:
                    raise RuntimeError('A component of the orthogonality graph is not bipartite!')

        self._orthogonality_graph = orthogonalityGraph
        check_again = False
        H = {self._edge_ordered(u,v):None for u,v in self._graph.edges(labels=False)}
        self._set_same_lengths(H, motion_types)

        for c in motion_types:
            if not orthogonalityGraph.has_edge(Set([c[0],c[2]]),Set([c[1],c[3]])):
                continue
            if motion_types[c]=='a':       # inconsistent since antiparallel motion cannot have orthogonal diagonals
                return False
            elif motion_types[c]=='p':     # this cycle must be rhombus
                self._set_two_edge_same_lengths(H, c[0], c[1], c[2], c[3], 0)
                self._set_two_edge_same_lengths(H, c[0], c[1], c[1], c[2], 0)
                self._set_two_edge_same_lengths(H, c[0], c[1], c[0], c[3], 0)
                check_again = True

        for c in motion_types:
            if motion_types[c]=='g':
                labels = [H[self._edge_ordered(c[i-1],c[i])] for i in range(0,4)]
                if (not None in labels
                    and ((len(Set(labels))==2 and labels.count(labels[0])==2)
                        or len(Set(labels))==1)):
                    return False
                if (orthogonalityGraph.has_edge(Set([c[0],c[2]]),Set([c[1],c[3]]))
                    and True in [(H[self._edge_ordered(c[i-1], c[i])]==H[self._edge_ordered(c[i-2], c[i-1])]
                                  and H[self._edge_ordered(c[i-1],c[i])]!= None) for i in range(0,4)]):
                    return False

        if check_again:
            for K23_edges in [Graph(self._graph).subgraph(k23_ver).edges(labels=False) for k23_ver in self._graph.induced_K23s()]:
                if MotionClassifier._same_edge_lengths(H, K23_edges):
                    return False

        return True

    @doc_index("General methods")
    def possible_motion_types_and_active_NACs(self,
                                              comments = {},
                                              show_table=True,
                                              one_representative=True,
                                              tab_rows=False,
                                              keep_orth_failed=False,
                                              equations=False):
        r"""
        Wraps the function for consistent motion types, conditions on orthogonality of diagonals and splitting into equivalence classes.
        """
        types = self.consistent_motion_types()
        classes = self.motion_types_equivalent_classes(types)
        valid_classes = []
        
        motions = [ 'g','a','p','d']
        if one_representative:
            header = [['index', '#', 'motion types'] + motions + ['active NACs', 'comment']]
        else:
            header = [['index', '#', 'elem.', 'motion types'] + motions + ['active NACs', 'comment']]
        if equations:
            header[0].append('equations')
        rows = []
        for i, cls in enumerate(classes):
            rows_cls = []
            to_be_appended = True
            for j, t in enumerate(cls):
                row = [i, len(cls)]
                if not one_representative:
                    row.append(j)
                row.append(' '.join([t[c] for c in self.four_cycles_ordered()]))
                row += [Counter([('d' if s in ['e','o'] else s) for c, s in t.items()])[m] for m in motions]
                try:
                    active = self.active_NAC_coloring_names(t)
                    row.append([self.mu(name) for name in sorted(active)])
                    if self.check_orthogonal_diagonals(t, active):
                        row.append(comments.get(i,''))
                    else:
                        to_be_appended = False
                        if not keep_orth_failed:
                            continue
                        else:
                            row.append('orthogonality check failed' + str(comments.get(i,'')))
                            
                except NotImplementedError as e:
                    zeros, eqs = self.consequences_of_nonnegative_solution_assumption(
                        flatten([self.ramification_formula(c, t[c]) for c in t]))
                    row.append([eq for eq in eqs if not eq in zeros])
                    row.append(str(comments.get(i,'')) + str(e))
                    
                if equations:
                    zeros, eqs = self.consequences_of_nonnegative_solution_assumption(
                        flatten([self.ramification_formula(c, t[c]) for c in t]))
                    row.append([eq for eq in eqs if not eq in zeros])
                    
                rows_cls.append(row)
                
                if one_representative:
                    break
            if to_be_appended or keep_orth_failed:
                valid_classes.append(cls)
                if one_representative:
                    rows += rows_cls
                else:
                    rows.append(rows_cls)
        if show_table:
            if one_representative:
                T = table(header + rows)
            else:
                T = table(header + [row for rows_cls in rows for row in rows_cls])
            T.options()['header_row'] = True
            display(T)

        if tab_rows:
            return valid_classes, rows
        return valid_classes
        

    @doc_index("Constraints on edge lengths")
    def motion_types2equations(self, motion_types,
                                           active_NACs=None,
                                           groebner_basis=True,
                                           extra_eqs=[]):
        r"""
        Return equations enforced by edge lengths and singleton active NAC-colorings.
        """
        if active_NACs==None:
            active_NACs = self.motion_types2active_NACs(motion_types)
        
        eqs_same_lengths = self.motion_types2same_lengths_equations(motion_types)
        eqs = flatten([self.equations_from_leading_coefs(delta, check=False,
                                                 extra_eqs=eqs_same_lengths + extra_eqs)
                    for delta in active_NACs if delta.is_singleton(active_NACs)
                ])
        if groebner_basis:
            return ideal(eqs).groebner_basis()
        else:
            return eqs
    
    @doc_index("General methods")
    def degenerate_triangle_equation(self, u, v, w):
        r"""
        Return the equation for a degenerate triangle.
        """
        return self.lam(u,v) - self.lam(u,w) - self.lam(w,v)
        

    @doc_index("Constraints on edge lengths")
    def motion_types2same_lengths_equations(self, motion_types):
        r"""
        Return the equations for edge lengths enforced by motion types.
        """
        eqs = []
        for c, motion in motion_types.items():
            if motion=='a' or motion=='p':
                eqs.append(self.lam(c[0], c[1]) - self.lam(c[2], c[3]))
                eqs.append(self.lam(c[1], c[2]) - self.lam(c[0], c[3]))
            elif motion=='o':
                eqs.append(self.lam(c[0], c[1]) - self.lam(c[1], c[2]))
                eqs.append(self.lam(c[2], c[3]) - self.lam(c[0], c[3]))
            elif motion=='e':
                eqs.append(self.lam(c[1], c[2]) - self.lam(c[2], c[3]))
                eqs.append(self.lam(c[0], c[1]) - self.lam(c[0], c[3]))
        return [eq for eq in ideal(eqs).groebner_basis()] if eqs else []


    @doc_index("Constraints on edge lengths")
    def graph_with_same_edge_lengths(self, motion_types, plot=True):
        r"""
        Return a graph with edge labels corresponding to same edge lengths.

        INPUT:
        
        - `plot` -- if `True` (default), then plot of the graph is returned. 
        
        OUTPUT:
        
        The edge labels of the output graph are same for if the edge lengths
        are same due to `motion_types`. 
        """
        H = {self._edge_ordered(u,v):None for u,v in self._graph.edges(labels=False)}
        self._set_same_lengths(H, motion_types)
        G_labeled = Graph([[u,v,H[(u,v)]] for u,v in H])
        G_labeled._pos = self._graph._pos
        if plot:
            return G_labeled.plot(edge_labels=True, color_by_label=True)
        else:
            return G_labeled

    @doc_index("Constraints on edge lengths")
    def singletons_table(self, active_NACs=None):
        r"""
        Return table whether (active) NAC-colorings are singletons.
        """
        rows = [['NAC-coloring', 'is singleton']]
        if active_NACs==None:
            active_NACs = self._graph.NAC_colorings()
            only_active = False
        else:
            only_active = True
            rows[0].append('is singleton w.r.t. active')

        for delta in active_NACs:
            rows.append([delta.name(), delta.is_singleton()])
            if only_active:
                rows[-1].append(delta.is_singleton(active_NACs))
        T = table(rows)
        T.options()['header_row'] = True
        return T
    
    @doc_index("System of equations for coordinates")
    def edge_equations_ideal(self, fixed_edge, eqs_lamdas=[], extra_eqs=[], show_input=False):
        r"""
        Return the ideal of equations for coordinates of vertices and given edge constraints.
        """
        equations = []
        for u,v in self._graph.edges(labels=False):
            equations.append((self.x(u)-self.x(v))**_sage_const_2 + (self.y(u)-self.y(v))**_sage_const_2 - self.l(u,v)**_sage_const_2)
        equations += [
            self.x(fixed_edge[0]),
            self.y(fixed_edge[0]),
            self.y(fixed_edge[1]),
            self.x(fixed_edge[1]) - self.l(fixed_edge[0], fixed_edge[1]),
            ] + [
                self._ring_coordinates(eq) for eq in list(eqs_lamdas) + list(extra_eqs)
                ]
        if show_input:
            for eq in equations:
                show(eq)
        return ideal(equations)
    
    @doc_index("General methods")
    def edge_lengths_dimension(self, eqs_lambdas):
        r"""
        Return the dimension of the variaty of edge lengths.
        """
        return ideal(eqs_lambdas + [self.aux_var]).dimension()
    
    @doc_index("Other")
    def edge_lengts_dict2eqs(self, edge_lengths):
        r"""
        Return equations with asigned edge lengths.
        """
        return [self.lam(e[0],e[1]) - QQ(edge_lengths[e]) for e in edge_lengths ]

    @doc_index("General methods")
    def edge_lengths_satisfy_eqs(self, eqs, edge_lengths, print_values=False):
        r"""
        Check if a given dictionary of edge lengths satisfy given equations.
        """
        I = ideal(self.edge_lengts_dict2eqs(edge_lengths))
        if print_values:
            print([(eq.reduce(I)) for eq in eqs])
        return sum([(eq.reduce(I))**2 for eq in eqs])==0

    
    @staticmethod
    @doc_index("Other")
    def show_factored_eqs(eqs, only_print=False, numbers=False,
                          variables=False, print_latex=False,
                          print_eqs=True):
        r"""
        Show given equations factored.
        """
        for i, eq in enumerate(eqs):
            factors = factor(eq)
            if numbers:
                print(i)
            if variables:
                print(latex(eq.variables()))
            if print_latex:
                print(latex(factors) + r'=0\,, \\\\')
            if print_eqs:
                if only_print:
                    print(factors)
                else:
                    show(factors)
    
    @staticmethod
    @doc_index("General methods")
    def is_subcase(eqs_a, eqs_b):
        r"""
        Return if `eqs_a` is a subcase of `eqs_b`, i.e., the ideal of `eqs_a` contains the ideal of `eqs_b`.
        """
        I_a = ideal(eqs_a)
        for eq in eqs_b:
            if not eq in I_a:
                return False
        return True
    
    @doc_index("Other")
    def motion_types2tikz(self,
                          motion_types,
                          color_names=[]
                          , vertex_style='lnodesmall',
                          none_gray=False,
                          ):
        r"""
        Return TikZ code for the graph with edges colored according to the lengths enforced by motion types.
        """
        H = {self._edge_ordered(u,v):None for u,v in self._graph.edges(labels=False)}
        self._set_same_lengths(H, motion_types)
        edge_partition = [[e for e in H if H[e]==el] for el in Set(H.values()) if el!=None]
        if none_gray:
            edge_partition.append([e for e in H if H[e]==None]) 
        else:
            edge_partition += [[e] for e in H if H[e]==None]
        if color_names==[]:
            color_names = ['edge, col{}'.format(i) for i in range(1,len(edge_partition)+1)]
        if none_gray:
            color_names[-1] = 'edge'

        self._graph.print_tikz(colored_edges= edge_partition,
                               color_names=color_names[:len(edge_partition)],
                               vertex_style=vertex_style)
    
__doc__ = __doc__.replace(
    "{INDEX_OF_METHODS}", gen_thematic_rest_table_index(MotionClassifier))
