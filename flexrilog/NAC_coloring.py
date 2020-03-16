# -*- coding: utf-8 -*-
r"""
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
-  Jan Legerský (2020-03-12): update to SageMath 9.0

NACcoloring
-----------
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

from sage.all import Graph, Set#, show
from sage.all import SageObject, latex, flatten
from sage.misc.rest_index_of_methods import gen_rest_table_index
from sage.misc.latex import latex_variable_name
from sage.all import PermutationGroup
from sage.all import copy


class NACcoloring(SageObject):
    r"""
    The class for a NAC-coloring of a graph.

    A coloring of edges $\\delta\\colon  E_G\\rightarrow \\{\\text{blue, red}\\}$
    is called a *NAC-coloring*, if it is surjective and for every cycle $C$ in $G$,
    either all edges of $C$ have the same color, or
    $C$ contains at least 2 edges in each color [GLS2018]_.

    INPUT:

    - ``G`` -- a graph of type :class:`FlexRiGraph`
      to which the NAC-coloring belongs.
    - ``coloring`` -- a dictionary assigning to every edge of ``G`` either ``"red"`` or ``"blue"``,
      or a list consisting of two lists giving a partition of the edges of ``G``
    - ``name`` -- an optional name of the NAC-coloring
    - ``check`` -- if ``True`` (default), then surjectivity and the cycle conditions are checked.
      (see :meth:`is_NAC_coloring`). A ``ValueError`` is raised if the check fails

    EXAMPLES::

        sage: from flexrilog import NACcoloring
        sage: from flexrilog import GraphGenerator
        sage: G = GraphGenerator.SmallestFlexibleLamanGraph(); G
        SmallestFlexibleLamanGraph: FlexRiGraph with the vertices [0, 1, 2, 3, 4] and edges [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 4), (3, 4)]
        sage: delta = NACcoloring(G,[[(0, 1), (0, 2), (0, 3), (1, 2), (1, 3)], [(2, 4), (3, 4)]]); delta
        NAC-coloring with red edges [[0, 1], [0, 2], [0, 3], [1, 2], [1, 3]] and blue edges [[2, 4], [3, 4]]

    By default, it is checked whether the ``coloring`` is a NAC-coloring::

        sage: delta = NACcoloring(G,[[(0, 1), (0, 2)], [(0, 3), (1, 2), (1, 3), (2, 4), (3, 4)]]); delta
        Traceback (most recent call last):
        ...
        ValueError: The coloring is not a NAC-coloring.
        sage: delta = NACcoloring(G,[[(0, 1), (0, 2)], [(0, 3), (1, 2), (1, 3), (2, 4), (3, 4)]], check=False); delta
        NAC-coloring with red edges [[0, 1], [0, 2]] and blue edges [[0, 3], [1, 2], [1, 3], [2, 4], [3, 4]]
        sage: delta.is_NAC_coloring()
        False

    A dictionary can be also used as an input::

        sage: delta = NACcoloring(G,{(0, 1) : "red", (0, 2) : "red", (0, 3) : "red", (1, 2) : "red", (1, 3) : "red", (2, 4) : "blue", (3, 4) : "blue"}); delta
        NAC-coloring with red edges [[0, 1], [0, 2], [0, 3], [1, 2], [1, 3]] and blue edges [[2, 4], [3, 4]]

    The ``coloring`` must be a partition of edges of ``G``::

        sage: delta = NACcoloring(G,[[(0, 1), (0, 2), (0, 3), (1, 3)], [(2, 4), (3, 4)]]); delta
        Traceback (most recent call last):
        ...
        RuntimeError: The edges of the NAC-coloring do not match the edges of the graph.
    """
    def __init__(self, G, coloring, name=None, check=True):
        from .flexible_rigid_graph import FlexRiGraph
        if type(G) == FlexRiGraph or 'FlexRiGraph' in str(type(G)) or isinstance(G, FlexRiGraph):
            self._graph = G
        else:
            raise TypeError('The graph G must be FlexRiGraph.')
        if type(coloring) in [list, Set] and len(coloring) == 2:
            self._red_edges = Set([Set(e) for e in coloring[0]])
            self._blue_edges = Set([Set(e) for e in coloring[1]])
        elif type(coloring) == dict:
            self._red_edges = Set([Set(e) for e in coloring if coloring[e] == 'red'])
            self._blue_edges = Set([Set(e) for e in coloring if coloring[e] == 'blue'])
        elif type(coloring)==NACcoloring or isinstance(coloring, NACcoloring) or 'NACcoloring' in str(type(coloring)):
            self._red_edges = copy(coloring._red_edges)
            self._blue_edges = copy(coloring._blue_edges)
        else:
            raise TypeError('The coloring must be a dict, list consisting of two lists or an instance of NACcoloring.')
        self._check_edges()
        self._name = name
        if check and not self.is_NAC_coloring():
            raise ValueError('The coloring is not a NAC-coloring.')

    def _repr_(self):
        """
        Return a string representation of `self`.
        """
        res = (self._name + ': ') if self._name != None else ''
        res += 'NAC-coloring with '
        if len(self._blue_edges) + len(self._red_edges) < 10:
            res += 'red edges ' + str(sorted([sorted(list(e)) for e in self._red_edges]))
            res += ' and blue edges ' + str(sorted([sorted(list(e)) for e in self._blue_edges]))
        else:
            res += str(len(self._red_edges)) + ' red edges and '
            res += str(len(self._blue_edges)) + ' blue edges '
        return res

    def name(self):
        r"""
        Return the name of the NAC-coloring.
        """
        return self._name if self._name != None else ''

    def _rich_repr_(self, display_manager, **kwds):
        # copied from GenericGraph
        prefs = display_manager.preferences
        is_small = (0 < self._graph.num_verts() < 20)
        can_plot = (prefs.supplemental_plot != 'never')
        plot_graph = can_plot and (prefs.supplemental_plot == 'always' or is_small)
        # Under certain circumstances we display the plot as graphics
        if plot_graph:
            output = self.plot()._rich_repr_(display_manager)
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
            l_name = latex_variable_name(self._name) + ': \\left( \\{'
        else:
            l_name = '\\left( \\{'
        return (l_name +','.join(['\\{' + latex(u) +','+ latex(v) + '\\}' 
                            for u,v in sorted([sorted(list(e)) for e in self._red_edges])])
                        + r'\} \mapsto red; \{'
                        + ','.join(['\\{' + latex(u) +','+ latex(v) + '\\}' 
                            for u,v in sorted([sorted(list(e)) for e in self._blue_edges])])
                        + r'\} \mapsto blue\right)')

    def _check_edges(self):
        r"""
        Raise a ``RuntimeError`` if the edges of the NAC-coloring do not match the edges of the graph.
        """
        if (Set([Set(e) for e in self._graph.edges(labels=False)])
            != self._blue_edges.union(self._red_edges)):
            raise RuntimeError('The edges of the NAC-coloring do not match the edges of the graph.')

    def is_NAC_coloring(self):
        r"""
        Return if the coloring is a NAC-coloring.

        The implementation uses Lemma 2.4 in [GLS2018]_.

        EXAMPLES::

            sage: from flexrilog import NACcoloring, GraphGenerator
            sage: G = GraphGenerator.SmallestFlexibleLamanGraph(); G
            SmallestFlexibleLamanGraph: FlexRiGraph with the vertices [0, 1, 2, 3, 4] and edges [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 4), (3, 4)]
            sage: delta = NACcoloring(G,[[(0, 1), (0, 2), (0, 3), (1, 2), (1, 3)], [(2, 4), (3, 4)]], check=False)
            sage: delta.is_NAC_coloring()
            True

        NAC-coloring must be surjective::

            sage: delta = NACcoloring(G,[[], [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 4), (3, 4)]], check=False)
            sage: delta.is_NAC_coloring()
            False

        And it has to satisfy the cycle conditions::

            sage: delta = NACcoloring(G,[[(0, 1), (0, 2)], [(0, 3), (1, 2), (1, 3), (2, 4), (3, 4)]], check=False)
            sage: delta.is_NAC_coloring()
            False

        """
        self._check_edges()

        if len(self._red_edges) == 0 or len(self._blue_edges) == 0:
            return False
        for one_color_subgraph in [self.red_subgraph(), self.blue_subgraph()]:
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

    def color(self, u, v=None):
        r"""
        Return the color of an edge.

        INPUT:

        If ``v`` is ``None``, then ``u`` is consider to be an edge.
        Otherwise, ``uv`` is taken as the edge.

        EXAMPLES::

            sage: from flexrilog import FlexRiGraph
            sage: G = FlexRiGraph(graphs.CompleteBipartiteGraph(3,3))
            sage: delta = G.NAC_colorings()[0]
            sage: delta.color(0,3)
            'red'
            sage: delta.color([2,4])
            'blue'
            sage: delta.color(1,2)
            Traceback (most recent call last):
            ...
            ValueError: There is no edge [1, 2]

        """
        if not v is None:
            if not self._graph.has_edge(u,v):
                raise ValueError('There is no edge ' + str([u,v]))
            return 'red' if Set([u,v]) in self._red_edges else 'blue'
        else:
            if not self._graph.has_edge(u[0],u[1]):
                raise ValueError('There is no edge ' + str([u[0],u[1]]))
            return 'red' if Set([u[0],u[1]]) in self._red_edges else 'blue'


    def red_edges(self):
        r"""
        Return the list of red edges of the NAC-coloring.
        """
        return list(self._red_edges)

    def is_red(self, u, v=None):
        r"""
        Return if the edge is red.

        INPUT:

        If ``v`` is ``None``, then ``u`` is consider to be an edge.
        Otherwise, ``uv`` is taken as the edge.

        EXAMPLES::

            sage: from flexrilog import FlexRiGraph
            sage: G = FlexRiGraph(graphs.CompleteBipartiteGraph(3,3))
            sage: delta = G.NAC_colorings()[0]
            sage: delta.is_red(0,3)
            True
            sage: delta.is_red([2,4])
            False
            sage: delta.is_red(1,2)
            Traceback (most recent call last):
            ...
            ValueError: There is no edge [1, 2]

        """
        if not v is None:
            if not self._graph.has_edge(u,v):
                raise ValueError('There is no edge ' + str([u,v]))
            return Set([u,v]) in self._red_edges
        else:
            if not self._graph.has_edge(u[0],u[1]):
                raise ValueError('There is no edge ' + str([u[0],u[1]]))
            return Set([u[0],u[1]]) in self._red_edges


    def is_blue(self, u, v=None):
        r"""
        Return if the edge is blue.

        INPUT:

        If ``v`` is ``None``, then ``u`` is consider to be an edge.
        Otherwise, ``uv`` is taken as the edge.

        EXAMPLES::

            sage: from flexrilog import FlexRiGraph
            sage: G = FlexRiGraph(graphs.CompleteBipartiteGraph(3,3))
            sage: delta = G.NAC_colorings()[0]
            sage: delta.is_blue(2,4)
            True
            sage: delta.is_blue([0,4])
            False
            sage: delta.is_blue(1,2)
            Traceback (most recent call last):
            ...
            ValueError: There is no edge [1, 2]

        """
        if v:
            if not self._graph.has_edge(u,v):
                raise ValueError('There is no edge ' + str([u,v]))
            return Set([u,v]) in self._blue_edges
        else:
            if not self._graph.has_edge(u[0],u[1]):
                raise ValueError('There is no edge ' + str([u[0],u[1]]))
            return Set([u[0],u[1]]) in self._blue_edges


    def blue_subgraph(self):
        return Graph([self._graph.vertices(),[list(e) for e in self._blue_edges]], format='vertices_and_edges')

    
    def blue_components(self):
        return self.blue_subgraph().connected_components()


    def red_subgraph(self):
        return Graph([self._graph.vertices(),[list(e) for e in self._red_edges]], format='vertices_and_edges')


    def red_components(self):
        return self.red_subgraph().connected_components()
    

    def plot(self, grid_pos=False, zigzag=False, **args_kwd):
        r"""
        Return a plot of the NAC-coloring.

        EXAMPLES::

            sage: from flexrilog import FlexRiGraph
            sage: G = FlexRiGraph(graphs.CompleteBipartiteGraph(3,3))
            sage: delta = G.NAC_colorings()[0]
            sage: delta.plot()
            Graphics object consisting of 16 graphics primitives

        .. PLOT::

            from flexrilog import FlexRiGraph
            G = FlexRiGraph(graphs.CompleteBipartiteGraph(3,3))
            sphinx_plot(G.NAC_colorings()[0])

        ::

            sage: from flexrilog import GraphGenerator
            sage: G = GraphGenerator.ThreePrismGraph()
            sage: delta = G.NAC_colorings()[0].conjugated()
            sage: delta.plot(grid_pos=True)
            Graphics object consisting of 16 graphics primitives

        .. PLOT::

            from flexrilog import GraphGenerator
            G = GraphGenerator.ThreePrismGraph()
            delta = G.NAC_colorings()[0].conjugated()
            sphinx_plot(delta.plot(grid_pos=True))

        ::

            sage: from flexrilog import GraphGenerator
            sage: G = GraphGenerator.ThreePrismGraph()
            sage: delta = G.NAC_colorings()[0].conjugated()
            sage: delta.plot(grid_pos=True, zigzag=True)
            Graphics object consisting of 16 graphics primitives

        .. PLOT::

            from flexrilog import GraphGenerator
            G = GraphGenerator.ThreePrismGraph()
            delta = G.NAC_colorings()[0].conjugated()
            sphinx_plot(delta.plot(grid_pos=True, zigzag=True))

        ::

            sage: from flexrilog import GraphGenerator
            sage: G = GraphGenerator.ThreePrismGraph()
            sage: delta = G.NAC_colorings()[0].conjugated()
            sage: delta.plot(grid_pos=True, zigzag=[[[0,0], [0,1]], [[0,0], [1,1/2], [2,0]]])
            Graphics object consisting of 16 graphics primitives

        .. PLOT::

            from flexrilog import GraphGenerator
            G = GraphGenerator.ThreePrismGraph()
            delta = G.NAC_colorings()[0].conjugated()
            sphinx_plot(delta.plot(grid_pos=True, zigzag=[[[0,0], [0,1]], [[0,0], [1,1/2], [2,0]]]))

        TODO:

        doc
        """
        if self.name():
            args_kwd['title'] = '$'+latex_variable_name(self.name())+'$'
        if grid_pos:
            from .graph_motion import GraphMotion
            args_kwd['pos'] = GraphMotion.GridConstruction(self._graph, self, zigzag).realization(0, numeric=True)
#            grid_coor = self.grid_coordinates()
#            if zigzag:
#                if type(zigzag) == list and len(zigzag) == 2:
#                    a = [vector(c) for c in zigzag[0]]
#                    b = [vector(c) for c in zigzag[1]]
#                else:
#                    m = max([k for _, k in grid_coor.values()])
#                    n = max([k for k, _ in grid_coor.values()])
#                    a = [vector([0.3*((-1)^i-1)+0.3*sin(i), i]) for i in range(0,m+1)]
#                    b = [vector([j, 0.3*((-1)^j-1)+0.3*sin(j)]) for j in range(0,n+1)]
#            else:
#                positions = {}
#                m = max([k for _, k in grid_coor.values()])
#                n = max([k for k, _ in grid_coor.values()])
#                a = [vector([0, i]) for i in range(0,m+1)]
#                b = [vector([j, 0]) for j in range(0,n+1)]
#            alpha = 0
#            rotation = matrix([[cos(alpha), sin(alpha)], [-sin(alpha), cos(alpha)]])
#            positions = {}
#            for v in self._graph.vertices():
#                positions[v] = rotation * a[grid_coor[v][1]] + b[grid_coor[v][0]]
#            return self._graph.plot(NAC_coloring=self, pos=positions)
        return self._graph.plot(NAC_coloring=self, name_in_title=False, **args_kwd)

    def is_isomorphic(self, other_coloring, check=True, certificate=False, aut_group=None):
        r"""
        Return if the NAC-coloring is isomorphic to ``other_coloring``.

        NAC-colorings $\\delta_1$ and $\\delta_2$ of a graph $G$ are isomorphic if and only if
        there exists and automorphism $\\sigma$ of $G$ such that

        - $\\delta_1(uv) = \\text{red} \\iff \\delta_2(\\sigma(u),\\sigma(v)) = \\text{red}$ for all $uv\\in E_G$, or
        - $\\delta_1(uv) = \\text{blue} \\iff \\delta_2(\\sigma(u),\\sigma(v)) = \\text{red}$ for all $uv\\in E_G$.

        INPUT:

        - ``other_coloring`` -- a NAC-colorings that is checked to be isomorphic with this NAC-coloring.
        - ``check`` -- if ``True`` (default), then it is checked whether the NAC-colorings belong
          to the same graph.
        - ``certificate`` -- if ``False`` (default), then only boolean is returned.
          Otherwise, ``(True, sigma)`` resp. ``(false, None)`` is returned,
          where ``sigma`` is the graph automorphism mapping the NAC-coloring to the ``other_coloring``.

        EXAMPLES::

            sage: from flexrilog import FlexRiGraph, NACcoloring
            sage: G = FlexRiGraph(graphs.CompleteBipartiteGraph(3,3))
            sage: colorings = G.NAC_colorings()
            sage: col1, col2, col3 = colorings[4], colorings[5], colorings[7]
            sage: col1
            NAC-coloring with red edges [[0, 3], [0, 4], [1, 3], [1, 4], [2, 5]] and blue edges [[0, 5], [1, 5], [2, 3], [2, 4]]
            sage: col2
            NAC-coloring with red edges [[0, 3], [0, 4], [1, 5], [2, 3], [2, 4]] and blue edges [[0, 5], [1, 3], [1, 4], [2, 5]]
            sage: col3
            NAC-coloring with red edges [[0, 3], [0, 5], [1, 3], [1, 5], [2, 3], [2, 5]] and blue edges [[0, 4], [1, 4], [2, 4]]
            sage: col1.is_isomorphic(col2)
            True
            sage: _, sigma = col1.is_isomorphic(col2, certificate=True); sigma
            (0,2,1)
            sage: col1.isomorphic_NAC_coloring(sigma).is_equal(col2)
            True
            sage: col1.is_isomorphic(col3)
            False

        ``col1``:

        .. PLOT::

            from flexrilog import FlexRiGraph, NACcoloring
            G = FlexRiGraph(graphs.CompleteBipartiteGraph(3,3))
            sphinx_plot(G.NAC_colorings()[4])

        ``col2``:

        .. PLOT::

            from flexrilog import FlexRiGraph, NACcoloring
            G = FlexRiGraph(graphs.CompleteBipartiteGraph(3,3))
            sphinx_plot(G.NAC_colorings()[5])
        """
        if check and self._graph != other_coloring._graph:
            raise RuntimeError('The NAC-colorings must belong to the same graph.')

        if aut_group==None:
            aut_group = self._graph.automorphism_group()
        if (Set([len(self.blue_edges()), len(self.red_edges())])
            != Set([len(other_coloring.blue_edges()), len(other_coloring.red_edges())])):
            if not certificate:
                return False
            else:
                return (False, None)

        for sigma in aut_group:
            if Set([self._red_edges, self._blue_edges]) == Set(other_coloring.isomorphic_NAC_coloring(sigma,onlySets=True)):
                if not certificate:
                    return True
                else:
                    return (True, sigma.inverse())
        if not certificate:
            return False
        else:
            return (False, None)

    def isomorphic_NAC_coloring(self, sigma, onlySets=False):
        r"""
        Return the NAC-coloring under a morphism ``sigma``.
        """
        if onlySets:
            return [Set([Set([sigma(e[0]),sigma(e[1])]) for e in self._red_edges]),
                    Set([Set([sigma(e[0]),sigma(e[1])]) for e in self._blue_edges])]
        else:
            return NACcoloring(self._graph, [[[sigma(e[0]),sigma(e[1])] for e in edges] for edges in [self._red_edges, self._blue_edges]])

    def is_equal(self, other_coloring, moduloConjugation=True):
        r"""
        Return if the NAC-coloring is equal to ``other_coloring``.

        INPUT:

        - ``moduloConjugation`` -- If ``True`` (default),
          then the NAC-colorings are compared modulo swapping colors.

        EXAMPLES::

            sage: from flexrilog import NACcoloring, GraphGenerator
            sage: G = GraphGenerator.SmallestFlexibleLamanGraph(); G
            SmallestFlexibleLamanGraph: FlexRiGraph with the vertices [0, 1, 2, 3, 4] and edges [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 4), (3, 4)]
            sage: delta1 = NACcoloring(G,[[(0, 1), (0, 2), (0, 3), (1, 2), (1, 3)], [(2, 4), (3, 4)]])
            sage: delta2 = NACcoloring(G,[[(2, 4), (3, 4)],[(0, 1), (0, 2), (0, 3), (1, 2), (1, 3)]])
            sage: delta1.is_equal(delta2)
            True
            sage: delta1.is_equal(delta2, moduloConjugation=False)
            False
        """
        if moduloConjugation:
            return Set([self._red_edges, self._blue_edges]) == Set([other_coloring._red_edges, other_coloring._blue_edges])
        else:
            return self._red_edges == other_coloring._red_edges and self._blue_edges == other_coloring._blue_edges


    def set_name(self, new_name):
        r"""
        Set a new name.

        EXAMPLES::

            sage: from flexrilog import GraphGenerator
            sage: G = GraphGenerator.SmallestFlexibleLamanGraph()
            sage: delta = G.NAC_colorings()[0]; delta
            NAC-coloring with red edges [[0, 1], [0, 2], [0, 3], [1, 2], [1, 3]] and blue edges [[2, 4], [3, 4]]
            sage: delta.set_name('delta'); delta
            delta: NAC-coloring with red edges [[0, 1], [0, 2], [0, 3], [1, 2], [1, 3]] and blue edges [[2, 4], [3, 4]]
            sage: latex(delta)
            \delta: \left( \{\{ 0 , 1 \},\{ 0 , 2 \},\{ 0 , 3 \},\{ 1 , 2 \},\{ 1 , 3 \}\} \mapsto red; 
            \{\{ 2 , 4 \},\{ 3 , 4 \}\} \mapsto blue\right)
        """
        self._name = new_name

    def path_is_unicolor(self, path):
        r"""
        Return if the edges of the path have the same color.
        """
        edges = Set([Set(e) for e in zip(path[:-1],path[1:])])
        return edges.issubset(self._red_edges) or edges.issubset(self._blue_edges)


    def grid_coordinates(self, ordered_red=[], ordered_blue=[]):
        r"""
        Return coordinates for the grid construction.
        
        The optional parameters `ordered_red`, `ordered_blue` can be used to specify the order of components to be taken.

        See [GLS2018]_ for the description of the grid construction.
        
        TODO:
        
        test
        """
        pos = {}
        red_comps = self.red_components()
        blue_comps = self.blue_components()
        if ordered_red:
            if type(ordered_red)!=list or len(ordered_red)!=len(red_comps) or Set(flatten(ordered_red))!=Set(self._graph.vertices()):
                raise ValueError('`ordered_red` must be a list of all red components, not ' + str(ordered_red))
            red_comps = ordered_red
        if ordered_blue:
            if type(ordered_blue)!=list or len(ordered_blue)!=len(blue_comps) or Set(flatten(ordered_blue))!=Set(self._graph.vertices()):
                raise ValueError('`ordered_blue` must be a list of all blue components, not ' + str(ordered_blue))
            blue_comps = ordered_blue
        for (i,red) in enumerate(red_comps):
            for (j,blue) in enumerate(blue_comps):
                for v in blue:
                    if v in red:
                        pos[v] = (i,j)
        return pos

    def grid_coordinates_are_injective(self):
        r"""
        Return if the grid coordinates are injective.

        EXAMPLES::

            sage: from flexrilog import GraphGenerator
            sage: G = GraphGenerator.ThreePrismGraph()
            sage: delta = G.NAC_colorings()[0]
            sage: delta.grid_coordinates_are_injective()
            True

        ::

            sage: from flexrilog import GraphGenerator
            sage: G = GraphGenerator.SmallestFlexibleLamanGraph()
            sage: delta = G.NAC_colorings()[0]
            sage: delta.grid_coordinates_are_injective()
            False
            """
        return len(Set(self.grid_coordinates().values())) == self._graph.num_verts()

    def conjugated(self):
        r"""
        Return the conjugated NAC-coloring.
        """
        return NACcoloring(self._graph, [self.blue_edges(), self.red_edges()], check=False)


    def is_singleton(self, NACs=[]):
        r"""
        Return if the NAC-coloring is a singleton.

        Let $G$ be a graph and $N$ be a subset of its NAC-colorings.
        A NAC-coloring $\\delta$ is called *singleton* w.r.t.\ $N$
        if $|\\{(\\delta(e),\\delta'(e))\\colon e\\in E_{Q_1}\\}|\\,\\neq 3$ for all $\\delta'\\in N$.

        INPUT:

        - ``NACs`` -- being singleton is considered w.r.t the list of NAC-colorings ``NACs``.
          If this is empty (default), then all NAC-colorings of the graph are considered.

        EXAMPLES::

            sage: from flexrilog import GraphGenerator
            sage: T = GraphGenerator.ThreePrismGraph()
            sage: delta = T.NAC_colorings()[0]
            sage: delta.is_singleton()
            True

        ::

            sage: Q1 = GraphGenerator.Q1Graph()
            sage: [[(delta.name(), delta.is_singleton()) for delta in equiv_cls] for equiv_cls in Q1.NAC_colorings_isomorphism_classes()]
            [[('psi2', False), ('psi1', False)],
             [('eta', True)],
             [('gamma1', True), ('gamma2', True)],
             [('phi4', False), ('phi3', False)],
             [('epsilon24', True),
              ('epsilon13', True),
              ('epsilon23', True),
              ('epsilon14', True)],
             [('zeta', False)]]

        ::

            sage: delta = Q1.name2NAC_coloring('psi1')
            sage: delta.is_singleton([Q1.name2NAC_coloring(name) for name in ['epsilon23', 'epsilon24', 'epsilon13', 'epsilon14']])
            True
        """
        if NACs == []:
            NACs = self._graph.NAC_colorings()
        for delta in NACs:
            if len(Set([(self.is_red(e), delta.is_red(e)) for e in self._graph.edges(labels=False)])) == 3:
                return False
        return True

    def cycle_has_orthogonal_diagonals(self, cycle):
        r"""
        Return if the NAC-coloring implies orthogonal diagonals for a given 4-cycle.

        EXAMPLE::

            sage: from flexrilog import GraphGenerator
            sage: K33 = GraphGenerator.K33Graph()
            sage: [[delta.name(), [cycle for cycle in K33.four_cycles() if delta.cycle_has_orthogonal_diagonals(cycle)]] for delta in K33.NAC_colorings()]
            [['omega5', []],
             ['omega3', []],
             ['omega1', []],
             ['omega6', []],
             ['epsilon56', [(1, 2, 3, 4)]],
             ['epsilon36', [(1, 2, 5, 4)]],
             ['epsilon16', [(2, 3, 4, 5)]],
             ['omega4', []],
             ['epsilon45', [(1, 2, 3, 6)]],
             ['epsilon34', [(1, 2, 5, 6)]],
             ['epsilon14', [(2, 3, 6, 5)]],
             ['omega2', []],
             ['epsilon25', [(1, 4, 3, 6)]],
             ['epsilon23', [(1, 4, 5, 6)]],
             ['epsilon12', [(3, 4, 5, 6)]]]
        """
        if len(cycle)!= 4:
            raise ValueError('The cycle must be a 4-cycle.')
        if self.path_is_unicolor(list(cycle) + [cycle[0]]):
            if self.is_red(cycle[0], cycle[1]):
                subgraph = Graph([self._graph.vertices(), [list(e) for e in self.blue_edges()]],  format='vertices_and_edges')
            else:
                subgraph = Graph([self._graph.vertices(), [list(e) for e in self.red_edges()]],  format='vertices_and_edges')
            if subgraph.shortest_path(cycle[0], cycle[2]) and subgraph.shortest_path(cycle[1], cycle[3]):
                return True
            else:
                return False
        return False

    def print_tikz(self):
        r"""
        Print TikZ code for the graph colored with the NAC-coloring.
        """
        self._graph.print_tikz([self.blue_edges(), self.red_edges()], ['redge', 'bedge'])
        
    def NAC2int(self):
        r"""
        Return the integer representation of the NAC-coloring.

        The binary representation of the number is obtained by sorting
        the edges lexicographically and setting 1 for red edges,
        0 for blue edges, or the other way around if the first edge is blue.
        
        EXAMPLE::
        
            sage: from flexrilog import GraphGenerator
            sage: delta = GraphGenerator.Q1Graph().NAC_colorings()[0]
            sage: delta.NAC2int()
            3871
            sage: 3871.binary()
            '111100011111'
        """
        s = '1'
        u1, v1 = self._graph.edges(labels=False)[0]
        first_color = self.color(u1, v1)
        for u,v in self._graph.edges(labels=False):
            s += '1' if self.color(u,v)==first_color else '0'
        return int(s,2)


__doc__ = __doc__.replace(
    "{INDEX_OF_METHODS}", (gen_rest_table_index(NACcoloring)))
