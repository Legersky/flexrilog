# -*- coding: utf-8 -*-
r"""
NAC-colorings
=========================

This class implements a NAC-coloring of a graph.

A coloring of edges $\\delta\\colon  E_G\\rightarrow \\{\\text{blue, red}\\}$ 
is called a *NAC-coloring*, if it is surjective and for every cycle $C$ in $G$,
either all edges of $C$ have the same color, or
$C$ contains at least 2 edges in each color [GLS2018]_.

Methods
-------


{INDEX_OF_METHODS}

AUTHORS:

-  Jan Legerský (2019-01-15): initial version

Class
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

from sage.all import Graph, Set, ceil, sqrt, matrix, deepcopy, copy
from sage.all import Subsets, SageObject, rainbow, latex
from sage.misc.rest_index_of_methods import doc_index, gen_thematic_rest_table_index
from sage.rings.integer import Integer
from sage.rings.rational import Rational
from sage.misc.latex import latex_variable_name

import exceptions

class NACcoloring(SageObject):
    r"""
    The class for a NAC-coloring of a graph.

    A coloring of edges $\\delta\\colon  E_G\\rightarrow \\{\\text{blue, red}\\}$ 
    is called a *NAC-coloring*, if it is surjective and for every cycle $C$ in $G$,
    either all edges of $C$ have the same color, or
    $C$ contains at least 2 edges in each color [GLS2018]_.

    INPUT:

    - ``G`` -- a graph of type :meth:`RigidFlexibleGraph` 
      to which the NAC-coloring belongs.
    - ``coloring`` -- a dictionary assigning to every edge of ``G`` either ``"red"`` or ``"blue"``,
      or a list consisting of two lists giving a partition of the edges of ``G``
    - ``name`` -- an optional name of the NAC-coloring
    - ``check`` -- if ``True`` (default), then surjectivity and the cycle conditions are checked.
      (see :meth:`is_NACcoloring`). A ``ValueError`` is raised if the check fails

    EXAMPLES::

        sage: from rigid_and_flexible_graphs.NAC_coloring import NACcoloring
        sage: from rigid_and_flexible_graphs.graph_generator import GraphGenerator
        sage: G = GraphGenerator.SmallestFlexibleLamanGraph(); G
        SmallestFlexibleLamanGraph: RigidFlexibleGraph with the vertices [0, 1, 2, 3, 4] and edges [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 4), (3, 4)]
        sage: delta = NACcoloring(G,[[(0, 1), (0, 2), (0, 3), (1, 2), (1, 3)], [(2, 4), (3, 4)]]); delta
        NAC-coloring with red edges {{1, 3}, {1, 2}, {0, 2}, {0, 3}, {0, 1}} and blue edges {{2, 4}, {3, 4}}

    By default, it is checked whether the ``coloring`` is a NAC-coloring::

        sage: delta = NACcoloring(G,[[(0, 1), (0, 2)], [(0, 3), (1, 2), (1, 3), (2, 4), (3, 4)]]); delta
        Traceback (most recent call last):
        ...
        ValueError: The coloring is not a NAC-coloring.
        sage: delta = NACcoloring(G,[[(0, 1), (0, 2)], [(0, 3), (1, 2), (1, 3), (2, 4), (3, 4)]], check=False); delta
        NAC-coloring with red edges {{0, 2}, {0, 1}} and blue edges {{1, 3}, {1, 2}, {2, 4}, {0, 3}, {3, 4}}
        sage: delta.is_NACcoloring()
        False

    A dictionary can be also used as an input::

        sage: delta = NACcoloring(G,{(0, 1) : "red", (0, 2) : "red", (0, 3) : "red", (1, 2) : "red", (1, 3) : "red", (2, 4) : "blue", (3, 4) : "blue"}); delta
        NAC-coloring with red edges {{1, 3}, {1, 2}, {0, 2}, {0, 3}, {0, 1}} and blue edges {{2, 4}, {3, 4}}

    The ``coloring`` must be a partition of edges of ``G``::

        sage: delta = NACcoloring(G,[[(0, 1), (0, 2), (0, 3), (1, 3)], [(2, 4), (3, 4)]]); delta
        Traceback (most recent call last):
        ...
        RuntimeError: The edges of the NAC-coloring do not match the edges of the graph.

    """
    def __init__(self, G, coloring, name=None, check=True):
        from rigid_flexible_graph import RigidFlexibleGraph
        if type(G) == RigidFlexibleGraph:
            self._graph = G
        else:
            raise exceptions.TypeError('The graph G must be RigidFlexibleGraph.')
        if type(coloring) in [list, Set] and len(coloring) == 2:
            self._red_edges = Set([Set(e) for e in coloring[0]])
            self._blue_edges = Set([Set(e) for e in coloring[1]])
        elif type(coloring) == dict:
            self._red_edges = Set([Set(e) for e in coloring if coloring[e] == 'red'])
            self._blue_edges = Set([Set(e) for e in coloring if coloring[e] == 'blue'])
        else:
            raise exceptions.TypeError('The coloring must be a dict or list consisting of two lists.')
        self._check_edges()
        self._name = name
        if check and not self.is_NACcoloring():
            raise exceptions.ValueError('The coloring is not a NAC-coloring.')

    def _repr_(self):
        res = (self._name + ': ') if self._name != None else ''
        res += 'NAC-coloring with '
        if len(self._blue_edges) + len(self._red_edges) < 10:
            res += 'red edges ' + str(self._red_edges)
            res += ' and blue edges ' + str(self._blue_edges)
        else:
            res += str(len(self._red_edges)) + ' red edges and '
            res += str(len(self._blue_edges)) + ' blue edges '
        return res


    def _rich_repr_(self, display_manager, **kwds):
        # copied from GenericGraph
        prefs = display_manager.preferences
        is_small = (0 < self._graph.num_verts() < 20)
        can_plot = (prefs.supplemental_plot != 'never')
        plot_graph = can_plot and (prefs.supplemental_plot == 'always' or is_small)
        # Under certain circumstances we display the plot as graphics
        if plot_graph:
            plot_kwds = dict(kwds)
            plot_kwds.setdefault('title', '$'+latex(self)+'$')
            output = self._graph.plot(NAC_coloring=self,**plot_kwds)._rich_repr_(display_manager)
            if output is not None:
                return output
        # create text for non-graphical output
        if can_plot:
            text = '{0} (use the .plot() method to plot)'.format(repr(self))
        else:
            text = repr(self)
        # latex() produces huge tikz environment, override
        tp = display_manager.types
        if (prefs.text == 'latex' and tp.OutputLatex in display_manager.supported_output()):
            return tp.OutputLatex(r'\text{{{0}}}'.format(text))
        return tp.OutputPlainText(text)


    def _latex_(self):
        if self._name:
            l_name = latex_variable_name(self._name) + ': \\left('
        else:
            l_name = '\\left('
        return l_name +latex(self._red_edges)+'\\mapsto red; '+latex(self._blue_edges)+'\\mapsto blue\\right)'

    def _check_edges(self):
        r"""
        Raise a ``RuntimeError`` if the edges of the NAC-coloring do not match the edges of the graph.
        """
        if (Set([Set(e) for e in self._graph.edges(labels=False)]) 
            != self._blue_edges.union(self._red_edges)):
            raise exceptions.RuntimeError('The edges of the NAC-coloring do not match the edges of the graph.')

    def is_NACcoloring(self):
        r"""
        Return if the coloring is a NAC-coloring.

        The implementation uses Lemma 2.4 in [GLS2018]_.

        EXAMPLES::

            sage: from rigid_and_flexible_graphs.NAC_coloring import NACcoloring
            sage: from rigid_and_flexible_graphs.graph_generator import GraphGenerator
            sage: G = GraphGenerator.SmallestFlexibleLamanGraph(); G
            SmallestFlexibleLamanGraph: RigidFlexibleGraph with the vertices [0, 1, 2, 3, 4] and edges [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 4), (3, 4)]
            sage: delta = NACcoloring(G,[[(0, 1), (0, 2), (0, 3), (1, 2), (1, 3)], [(2, 4), (3, 4)]], check=False)
            sage: delta.is_NACcoloring()
            True

        NAC-coloring must be surjective::

            sage: delta = NACcoloring(G,[[], [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 4), (3, 4)]], check=False)
            sage: delta.is_NACcoloring()
            False

        And it has to satisfy the cycle conditions::

            sage: delta = NACcoloring(G,[[(0, 1), (0, 2)], [(0, 3), (1, 2), (1, 3), (2, 4), (3, 4)]], check=False)
            sage: delta.is_NACcoloring()
            False

        """
        self._check_edges()

        if len(self._red_edges) == 0 or len(self._blue_edges) == 0:
            return False
        for edges in [self._red_edges, self._blue_edges]:
            one_color_subgraph = Graph([list(e) for e in edges])
            for component in one_color_subgraph.connected_components():
                if (len(Graph(self._graph).subgraph(component).edges(labels=False)) 
                    - len(one_color_subgraph.subgraph(component).edges(labels=False))):
                    return False
        return True

    def blue_edges(self):
        r"""
        Return the list of blue edges of the NAC-coloring.
        """
        return list(self._blue_edges)


    def red_edges(self):
        r"""
        Return the list of red edges of the NAC-coloring.
        """
        return list(self._red_edges)

    def plot(self):
        return self._graph.plot(NAC_coloring=self)

    def is_isomorphic(self, NAC_coloring, check=True):
        if check and self._graph != NAC_coloring._graph:
            raise exceptions.RuntimeError('The NAC-colorings must belong to the same graph.')
        for sigma in self._graph.automorphism_group():
            if self.is_equal(NAC_coloring.isomorphic_NAC_coloring(sigma)):
                return True
        return False

    def isomorphic_NAC_coloring(self, sigma):
        r"""
        Return isomorphic NAC-coloring under automorphism ``sigma``.
        """
        return NACcoloring(self._graph, [[[sigma(e[0]),sigma(e[1])] for e in edges] for edges in [self._red_edges, self._blue_edges]])

    def is_equal(self, NAC_coloring, moduloConjugation=True):
        r"""
        Return if the NAC-coloring is equal to ``NAC_coloring``.

        INPUT:

        - ``moduloConjugation`` -- If ``True`` (default),
          then the NAC-colorings are compared modulo swapping colors.

        """
        if moduloConjugation:
            return Set([self._red_edges, self._blue_edges]) == Set([NAC_coloring._red_edges, NAC_coloring._blue_edges])
        else:
            return self._red_edges == NAC_coloring._red_edges and self._blue_edges == NAC_coloring._blue_edges





_additional_categories = {
    #RigidFlexibleGraph.plot         : "Plotting",
    }
__doc__ = __doc__.replace(
    "{INDEX_OF_METHODS}", (gen_thematic_rest_table_index(NACcoloring, _additional_categories)))
