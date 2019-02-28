# -*- coding: utf-8 -*-
r"""
This is implementation of classification motions of a graph.

TODO:

- setdefault, defaultdict
- for ... else:
- substitute instead of Groebner basis


Methods
-------

{INDEX_OF_METHODS}


AUTHORS:

-  Jan Legerský (2019-02-18): initial version

Classes
-------
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

from sage.all import Graph, Set, Subsets, deepcopy#,, find_root ceil, sqrt, matrix, copy,
from sage.all import SageObject, PolynomialRing, QQ, flatten, ideal, sgn
#from sage.all import vector, matrix, sin, cos, pi,  var,  RR,  floor,  tan
#from sage.all import FunctionField, QQ,  sqrt,  function
from sage.misc.rest_index_of_methods import gen_rest_table_index
from sage.rings.integer import Integer
_sage_const_3 = Integer(3); _sage_const_2 = Integer(2); _sage_const_1 = Integer(1);
#_sage_const_0 = Integer(0); _sage_const_6 = Integer(6); _sage_const_5 = Integer(5);
#_sage_const_4 = Integer(4); _sage_const_13 = Integer(13); _sage_const_12 = Integer(12)
#from sage.rings.rational import Rational
from rigid_flexible_graph import RigidFlexibleGraph
import exceptions

class MotionClassifier(SageObject):
    def __init__(self, graph, four_cycles=[], separator=''):
        r"""
        """
        if not (isinstance(graph, RigidFlexibleGraph) or 'RigidFlexibleGraph' in str(type(graph))):
            raise exceptions.TypeError('The graph must be of the type RigidFlexibleGraph.')
        self._graph = graph

        if four_cycles == []:
            self._four_cycles = self._graph.four_cycles()
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

        for e in self._graph.edges(labels=False):
            ws.append('w' + self._edge2str(e))
            zs.append('z' + self._edge2str(e))
            lambdas.append('lambda' + self._edge2str(e))
            ws_latex.append('w_{' + self._edge2str(e).replace('_', separator) + '}')
            zs_latex.append('z_{' + self._edge2str(e).replace('_', separator) + '}')
            lambdas_latex.append('\\lambda_{' + self._edge2str(e).replace('_', separator) + '}')

        self._ringLC = PolynomialRing(QQ, names=ws+zs+lambdas, order='lex')
        self._ringLC._latex_names = ws_latex + zs_latex + lambdas_latex
        self._ringLC_gens = self._ringLC.gens_dict()

#        ----Ramification-----
        self._ring_ramification = PolynomialRing(QQ, names=[col.name() for col in self._graph.NAC_colorings()])
        self._ring_ramification_gens = self._ring_ramification.gens_dict()
        self._restriction_NAC_types = self.NAC_coloring_restrictions()

#        -----Graph of 4-cycles-----
        self._four_cycle_graph = Graph([self._four_cycles,[]], format='vertices_and_edges')

        for c1, c2 in Subsets(self._four_cycle_graph.vertices(), 2):
            intersection = self.cycle_edges(c1, sets=True).intersection(self.cycle_edges(c2, sets=True))
            if len(intersection)>=2 and len(intersection[0].intersection(intersection[1]))==1:
                common_vert = intersection[0].intersection(intersection[1])[0]
                self._four_cycle_graph.add_edge(c1, c2, common_vert)

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
    def cycle_edges(cycle, sets=False):
        if sets:
            return Set([Set(list(e)) for e in zip(cycle, list(cycle[1:])+[cycle[0]])])
        else:
            return [list(e) for e in zip(cycle, list(cycle[1:])+[cycle[0]])]

    def w(self, e):
        if e[0] < e[1]:
            return self._ringLC_gens['w'+self._edge2str(e)]
        else:
            return -self._ringLC_gens['w'+self._edge2str(e)]

    def z(self, e):
        if e[0] < e[1]:
            return self._ringLC_gens['z'+self._edge2str(e)]
        else:
            return -self._ringLC_gens['z'+self._edge2str(e)]

    def lam(self, e):
        return self._ringLC_gens['lambda'+self._edge2str(e)]

    def mu(self, delta):
        if type(delta)==str:
            return self._ring_ramification_gens[delta]
        else:
            return self._ring_ramification_gens[delta.name()]

    def equations_from_leading_coefs(self, col, extra_eqs=[], check=True):
        r"""
        Return equations for edge lengths from leading coefficients system.

        EXAMPLES::

            sage: from rigid_flexible_graph import RigidFlexibleGraph, MotionClassifier
            sage: K33 = RigidFlexibleGraph(graphs.CompleteBipartiteGraph(3,3))
            sage: M = MotionClassifier(K33)
            sage: M.equation_from_leading_coefs('beta1')
            [lambda0_3^2 - lambda0_4^2 - lambda1_3^2 + lambda1_4^2]

        ::

            sage: M.equation_from_leading_coefs('alpha1')
            ---------------------------------------------------------------------------
            ValueError                                Traceback (most recent call last):
            ...
            ValueError: The NAC-coloring must be a singleton.

        ::

            sage: MC.equations_from_leading_coefs('alpha1', check=False)
            [-lambda0_3^2*lambda1_4^2 + lambda0_3^2*lambda1_5^2 + lambda0_4^2*lambda1_3^2 - lambda0_4^2*lambda1_5^2 - lambda0_5^2*lambda1_3^2 + lambda0_5^2*lambda1_4^2]
        """

        if type(col) == str:
            col = self._graph.name2NAC_coloring(col)

        if check:
            if not col.is_singleton():
                raise exceptions.ValueError('The NAC-coloring must be a singleton.')
        eqs_lengths=[]
        for e in self._graph.edges():
            eqs_lengths.append(self.z(e)*self.w(e) - self.lam(e)**_sage_const_2)


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
                    if col.is_red(u,v):
                        eqz+=self.z([u,v])
                    else:
                        eqw+=self.w([u,v])
                    eqw_all+=self.w([u,v])
                    eqz_all+=self.z([u,v])
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
                     + extra_eqs)
        return ideal(equations).elimination_ideal(flatten([[self.w(e), self.z(e)] for e in self._graph.edges()])).basis

    @staticmethod
    def _pair_ordered(u,v):
        if u<v:
            return (u, v)
        else:
            return (v, u)

    @staticmethod
    def _edge_ordered(u,v):
        return MotionClassifier._pair_ordered(u, v)


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

    def NAC_coloring_restrictions(self):
        r"""
        Return types of restrictions of NAC-colorings to 4-cycles.

        EXAMPLE::

            sage: from rigid_and_flexible_graphs import MotionClassifier, GraphGenerator
            sage: MC = MotionClassifier(GraphGenerator.K33Graph())
            sage: MC.NAC_coloring_restrictions()
            {(1, 2, 3, 4): {'L': ['alpha3', 'alpha1', 'epsilon36', 'epsilon16'],
              'O': ['epsilon34', 'epsilon14', 'epsilon23', 'epsilon12'],
              'R': ['alpha4', 'epsilon45', 'alpha2', 'epsilon25']},
            ...
             (3, 4, 5, 6): {'L': ['alpha5', 'alpha3', 'epsilon25', 'epsilon23'],
              'O': ['epsilon56', 'epsilon36', 'epsilon45', 'epsilon34'],
              'R': ['alpha6', 'epsilon16', 'alpha4', 'epsilon14']}}
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

    def ramification_formula(self, cycle, motion):
        r"""
        Return ramification formula for a given 4-cycle and motion type.

        EXAMPLES::

            sage: from rigid_and_flexible_graphs import MotionClassifier, GraphGenerator
            sage: MC = MotionClassifier(GraphGenerator.K33Graph())
            sage: MC.ramification_formula((1,2,3,4), 'g')
            [epsilon12, epsilon23, epsilon14, epsilon34, omega3 + omega1 + epsilon36 + epsilon16 - omega4 - epsilon45 - omega2 - epsilon25]
        """
#        eqs = []
#        NAC_types = self.motion2NAC_types(motion)
#        for t in ['L','O','R']:
#            if t in NAC_types:
#                eqs.append(sum([self.mu(delta)-self.mu('d') for delta in self._restriction_NAC_types[cycle][t]]))
#            else:
#                eqs += [self.mu(delta) for delta in self._restriction_NAC_types[cycle][t]]
#        return ideal(eqs).elimination_ideal([self.mu('d')]).gens()

        eqs_present = []
        eqs_zeros = []
        NAC_types = self.motion2NAC_types(motion)
        for t in ['L','O','R']:
            if t in NAC_types:
                eqs_present.append(sum([self.mu(delta) for delta in self._restriction_NAC_types[cycle][t]]))
            else:
                eqs_zeros += [self.mu(delta) for delta in self._restriction_NAC_types[cycle][t]]
        if len(eqs_present)==2:
            return eqs_zeros + [eqs_present[0] - eqs_present[1]]
        elif len(eqs_present)==3:
            return eqs_zeros + [eqs_present[0] - eqs_present[1], eqs_present[1] - eqs_present[2]]
        else:
            return eqs_zeros

    @staticmethod
    def motion2NAC_types(m):
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

    @staticmethod
    def consequences_of_nonnegative_solution_assumption(eqs):
        n_zeros_prev = -1
        zeros = []
        gb = eqs
        while n_zeros_prev!=len(zeros):
            n_zeros_prev = len(zeros)
            gb = ideal(gb + zeros).groebner_basis()
            zeros = []
            for eq in gb:
                coefs = eq.coefficients()
                if sum([sgn(a)*sgn(b) for a,b in zip(coefs[:-1],coefs[1:])])==len(coefs)-1:
                    zeros += eq.variables()
        return [zeros, gb]

    def consistent_motion_types(self, cycles=[]):
        if cycles==[]:
            cycles = self.four_cycles_ordered()

        k23s = [Graph(self._graph).subgraph(k23_ver).edges(labels=False) for k23_ver in self._graph.induced_K23s()]

        aa_pp = [('a', 'a'), ('p', 'p')]
        ao = [self._pair_ordered('a','o')]
        ae = [self._pair_ordered('a','e')]
        oe = [self._pair_ordered('o', 'e')]
        oo_ee = [('e','e'), ('o','o')]

        H = {self._edge_ordered(u,v):None for u,v in self._graph.edges(labels=False)}
        types_prev=[[{}, []]]

        for i, new_cycle in enumerate(cycles):
            types_ext = []
            new_cycle_neighbors = [[c2,
                                    new_cycle.index(self._four_cycle_graph.edge_label(new_cycle, c2)),
                                    c2.index(self._four_cycle_graph.edge_label(new_cycle, c2)),
                                   ] for c2 in self._four_cycle_graph.neighbors(new_cycle) if c2 in cycles[:i]]
            for types_original, ramification_eqs_prev in types_prev:
                for type_new_cycle in ['g','a','p','o','e']:
                    types = deepcopy(types_original)
                    types[tuple(new_cycle)] = type_new_cycle
    #                 H = deepcopy(orig_graph)
                    fine = True

                    for c2, new_index, c2_index in new_cycle_neighbors:
                        type_pair = self._pair_ordered(types[new_cycle], types[c2])
                        if (type_pair in aa_pp
                                or (type_pair in oe and new_index%2 == c2_index%2)
                                or (type_pair in oo_ee and new_index%2 != c2_index%2)):
                            fine = False
                            break
                        if (type_pair in ao
                            and ((types[new_cycle]=='o' and new_index%2==1)
                            #odd deltoid (1,2,3,4) is consistent with 'a' if the common vertex is odd, but Python lists are indexed from 0
                                or (types[c2]=='o' and c2_index%2==1))):
                            fine = False
                            break
                        if (type_pair in ae
                            and ((types[new_cycle]=='e' and new_index%2==0)
                                or (types[c2]=='e' and c2_index%2==0))):
                            fine = False
                            break
                    if not fine:
                        continue

                    self._set_same_lengths(H, types)
                    for c in types:
                        if types[c]=='g':
                            labels = [H[self._edge_ordered(c[i-1],c[i])] for i in range(0,4)]
                            if (not None in labels
                                and ((len(Set(labels))==2 and labels.count(labels[0])==2)
                                    or len(Set(labels))==1)):
                                fine = False
                                break
                    if not fine:
                        continue
                    for K23_edges in k23s:
                        if MotionClassifier._same_edge_lengths(H, K23_edges):
                            fine = False
                            break
                    if not fine:
                        continue

                    ramification_eqs = ramification_eqs_prev + self.ramification_formula(new_cycle, type_new_cycle)
                    zero_variables, ramification_eqs = self.consequences_of_nonnegative_solution_assumption(ramification_eqs)
                    for cycle in types:
                        if not fine:
                            break
                        for t in self.motion2NAC_types(types[cycle]):
                            has_necessary_NAC_type = False
                            for delta in self._restriction_NAC_types[cycle][t]:
                                if not self.mu(delta) in zero_variables:
                                    has_necessary_NAC_type = True
                                    break
                            if not has_necessary_NAC_type:
                                fine = False
                                break
                    if not fine:
                        continue

                    types_ext.append([types, ramification_eqs])

            types_prev=types_ext

        return types_prev

    def active_NAC_colorings(self, motion_types, eqs=[]):
        if eqs==[]:
            zeros, eqs = self.consequences_of_nonnegative_solution_assumption([
                self.ramification_formula(c, motion_types[c]) for c in motion_types
            ])
        else:
            zeros = [eq for eq in eqs if eq.is_monomial()]
        if ideal(eqs).dimension()==1:
            return [delta for delta in self._graph.NAC_colorings() if not self.mu(delta) in zeros]
        else:
            raise NotImplementedError('If the dimension of the ideal is greater than one, it is not clear how to proceed.')

__doc__ = __doc__.replace(
    "{INDEX_OF_METHODS}", gen_rest_table_index(MotionClassifier))
