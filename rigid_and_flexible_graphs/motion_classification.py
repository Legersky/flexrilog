# -*- coding: utf-8 -*-
r"""
This is implementation of classification motions of a graph.

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

#from sage.all import deepcopy, Set, Graph, find_root#, ceil, sqrt, matrix, copy
from sage.all import SageObject, PolynomialRing, QQ, flatten, ideal
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
    def __init__(self, graph, separator=''):
        if not (isinstance(graph, RigidFlexibleGraph) or 'RigidFlexibleGraph' in str(type(graph))):
            raise exceptions.TypeError('The graph must be of the type RigidFlexibleGraph.')
        self._graph = graph

        if not self._graph.are_NAC_colorings_named():
            self._graph.set_NAC_colorings_names()
        Ws = []
        Zs = []
        lambdas = []
        Ws_latex = []
        Zs_latex = []
        lambdas_latex = []

        for e in self._graph.edges(labels=False):
            Ws.append('W' + self._edge2str(e))
            Zs.append('Z' + self._edge2str(e))
            lambdas.append('lambda' + self._edge2str(e))
            Ws_latex.append('W_{' + self._edge2str(e).replace('_', ',') + '}')
            Zs_latex.append('Z_{' + self._edge2str(e).replace('_', ',') + '}')
            lambdas_latex.append('\\lambda_{' + self._edge2str(e).replace('_', separator) + '}')

        self._ringLC = PolynomialRing(QQ, names=Ws+Zs+lambdas, order='lex')
        self._ringLC._latex_names = Ws_latex + Zs_latex + lambdas_latex

    def _repr_(self):
        return 'Motion Classifier of the graph ' + str(self._graph)

    @staticmethod
    def _edge2str(e):
        if e[0]<e[1]:
            return str(e[0]) + '_' + str(e[1])
        else:
            return str(e[1]) + '_' + str(e[0])

    def W(self, e):
        if e[0] < e[1]:
            return self._ringLC.gens_dict()['W'+self._edge2str(e)]
        else:
            return -self._ringLC.gens_dict()['W'+self._edge2str(e)]

    def Z(self, e):
        if e[0] < e[1]:
            return self._ringLC.gens_dict()['Z'+self._edge2str(e)]
        else:
            return -self._ringLC.gens_dict()['Z'+self._edge2str(e)]

    def lam(self, e):
        return self._ringLC.gens_dict()['lambda'+self._edge2str(e)]


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
            eqs_lengths.append(self.Z(e)*self.W(e) - self.lam(e)**_sage_const_2)


        eqs_W=[]
        eqs_Z=[]
        for T in self._graph.spanning_trees():
            for e in self._graph.edges():
                eqW = 0
                eqW_all = 0
                eqZ = 0
                eqZ_all = 0
                path = T.shortest_path(e[0],e[1])
                for u,v in zip(path, path[1:]+[path[0]]):
                    if col.is_red(u,v):
                        eqZ+=self.Z([u,v])
                    else:
                        eqW+=self.W([u,v])
                    eqW_all+=self.W([u,v])
                    eqZ_all+=self.Z([u,v])
                if eqW:
                    eqs_W.append(eqW)
                else:
                    eqs_W.append(eqW_all)
                if eqZ:
                    eqs_Z.append(eqZ)
                else:
                    eqs_Z.append(eqZ_all)

        equations = (ideal(eqs_W).groebner_basis()
                     + ideal(eqs_Z).groebner_basis()
                     + eqs_lengths
                     + extra_eqs)
        return ideal(equations).elimination_ideal(flatten([[self.W(e), self.Z(e)] for e in self._graph.edges()])).basis








__doc__ = __doc__.replace(
    "{INDEX_OF_METHODS}", gen_rest_table_index(MotionClassifier))
