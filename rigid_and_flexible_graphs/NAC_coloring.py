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

from sage.all import Graph, Set
from sage.all import SageObject, latex, flatten
from sage.misc.rest_index_of_methods import gen_rest_table_index
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
      (see :meth:`is_NAC_coloring`). A ``ValueError`` is raised if the check fails

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
        sage: delta.is_NAC_coloring()
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
        from .rigid_flexible_graph import RigidFlexibleGraph
        if type(G) == RigidFlexibleGraph or 'RigidFlexibleGraph' in str(type(G)):
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
        if check and not self.is_NAC_coloring():
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

    def is_NAC_coloring(self):
        r"""
        Return if the coloring is a NAC-coloring.

        The implementation uses Lemma 2.4 in [GLS2018]_.

        EXAMPLES::

            sage: from rigid_and_flexible_graphs.NAC_coloring import NACcoloring
            sage: from rigid_and_flexible_graphs.graph_generator import GraphGenerator
            sage: G = GraphGenerator.SmallestFlexibleLamanGraph(); G
            SmallestFlexibleLamanGraph: RigidFlexibleGraph with the vertices [0, 1, 2, 3, 4] and edges [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 4), (3, 4)]
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

    def is_red(self, u, v=None):
        r"""
        Return if the edge is red.

        INPUT:

        If ``v`` is ``None``, then ``u`` is consider to be an edge.
        Otherwise, ``uv`` is taken as the edge.

        EXAMPLES::

            sage: from rigid_and_flexible_graphs.rigid_flexible_graph import RigidFlexibleGraph
            sage: G = RigidFlexibleGraph(graphs.CompleteBipartiteGraph(3,3))
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
        if v:
            if not self._graph.has_edge(u,v):
                raise exceptions.ValueError('There is no edge ' + str([u,v]))
            return Set([u,v]) in self._red_edges
        else:
            if not self._graph.has_edge(u[0],u[1]):
                raise exceptions.ValueError('There is no edge ' + str([u[0],u[1]]))
            return Set([u[0],u[1]]) in self._red_edges


    def is_blue(self, u, v=None):
        r"""
        Return if the edge is blue.

        INPUT:

        If ``v`` is ``None``, then ``u`` is consider to be an edge.
        Otherwise, ``uv`` is taken as the edge.

        EXAMPLES::

            sage: from rigid_and_flexible_graphs.rigid_flexible_graph import RigidFlexibleGraph
            sage: G = RigidFlexibleGraph(graphs.CompleteBipartiteGraph(3,3))
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
                raise exceptions.ValueError('There is no edge ' + str([u,v]))
            return Set([u,v]) in self._blue_edges
        else:
            if not self._graph.has_edge(u[0],u[1]):
                raise exceptions.ValueError('There is no edge ' + str([u[0],u[1]]))
            return Set([u[0],u[1]]) in self._blue_edges


    def plot(self, grid_pos=False, zigzag=False):
        r"""
        Return a plot of the NAC-coloring.

        EXAMPLES::

            sage: from rigid_and_flexible_graphs.rigid_flexible_graph import RigidFlexibleGraph
            sage: G = RigidFlexibleGraph(graphs.CompleteBipartiteGraph(3,3))
            sage: delta = G.NAC_colorings()[0]
            sage: delta.plot()
            Graphics object consisting of 16 graphics primitives

        .. PLOT::

            from rigid_and_flexible_graphs.rigid_flexible_graph import RigidFlexibleGraph
            G = RigidFlexibleGraph(graphs.CompleteBipartiteGraph(3,3))
            sphinx_plot(G.NAC_colorings()[0])

        ::

            sage: from rigid_and_flexible_graphs.graph_generator import GraphGenerator
            sage: G = GraphGenerator.ThreePrismGraph()
            sage: delta = G.NAC_colorings()[0].conjugated()
            sage: delta.plot(grid_pos=True)
            Graphics object consisting of 16 graphics primitives

        .. PLOT::

            from rigid_and_flexible_graphs.graph_generator import GraphGenerator
            G = GraphGenerator.ThreePrismGraph()
            delta = G.NAC_colorings()[0].conjugated()
            sphinx_plot(delta.plot(grid_pos=True))

        ::

            sage: from rigid_and_flexible_graphs.graph_generator import GraphGenerator
            sage: G = GraphGenerator.ThreePrismGraph()
            sage: delta = G.NAC_colorings()[0].conjugated()
            sage: delta.plot(grid_pos=True, zigzag=True)
            Graphics object consisting of 16 graphics primitives

        .. PLOT::

            from rigid_and_flexible_graphs.graph_generator import GraphGenerator
            G = GraphGenerator.ThreePrismGraph()
            delta = G.NAC_colorings()[0].conjugated()
            sphinx_plot(delta.plot(grid_pos=True, zigzag=True))

        ::

            sage: from rigid_and_flexible_graphs.graph_generator import GraphGenerator
            sage: G = GraphGenerator.ThreePrismGraph()
            sage: delta = G.NAC_colorings()[0].conjugated()
            sage: delta.plot(grid_pos=True, zigzag=[[[0,0], [0,1]], [[0,0], [1,1/2], [2,0]]])
            Graphics object consisting of 16 graphics primitives

        .. PLOT::

            from rigid_and_flexible_graphs.graph_generator import GraphGenerator
            G = GraphGenerator.ThreePrismGraph()
            delta = G.NAC_colorings()[0].conjugated()
            sphinx_plot(delta.plot(grid_pos=True, zigzag=[[[0,0], [0,1]], [[0,0], [1,1/2], [2,0]]]))

        TODO:
        
        doc
        """
        if grid_pos:
            from .graph_motion import GraphMotion
            return self._graph.plot(NAC_coloring=self,
                                    pos=GraphMotion.GridConstruction(self._graph, self, zigzag).realization(0, numeric=True))
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
        else:
            return self._graph.plot(NAC_coloring=self)

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
        - ``certificate`` -- if ``False`` (default), then onlt boolean is returned.
          Otherwise, ``(True, sigma)`` resp. ``(false, None)`` is returned,
          where ``sigma`` is the graph automorphism mapping the NAC-coloring to the ``other_coloring``.

        EXAMPLES::

            sage: from rigid_and_flexible_graphs.rigid_flexible_graph import RigidFlexibleGraph
            sage: from rigid_and_flexible_graphs.NAC_coloring import NACcoloring
            sage: G = RigidFlexibleGraph(graphs.CompleteBipartiteGraph(3,3))
            sage: colorings = G.NAC_colorings()
            sage: col1, col2, col3 = colorings[4], colorings[5], colorings[7]
            sage: col1
            NAC-coloring with red edges {{1, 3}, {0, 4}, {1, 4}, {0, 3}, {2, 5}} and blue edges {{2, 4}, {0, 5}, {1, 5}, {2, 3}}
            sage: col2
            NAC-coloring with red edges {{2, 4}, {0, 4}, {2, 3}, {0, 3}, {1, 5}} and blue edges {{1, 3}, {0, 5}, {2, 5}, {1, 4}}
            sage: col3
            NAC-coloring with red edges {{2, 3}, {2, 5}, {1, 3}, {1, 5}, {0, 5}, {0, 3}} and blue edges {{2, 4}, {0, 4}, {1, 4}}
            sage: col1.is_isomorphic(col2)
            True
            sage: _, sigma = col1.is_isomorphic(col2, certificate=True); sigma
            (1,2)
            sage: col1.isomorphic_NAC_coloring(sigma).is_equal(col2)
            True
            sage: col1.is_isomorphic(col3)
            False

        ``col1``:

        .. PLOT::

            from rigid_and_flexible_graphs.rigid_flexible_graph import RigidFlexibleGraph
            from rigid_and_flexible_graphs.NAC_coloring import NACcoloring
            G = RigidFlexibleGraph(graphs.CompleteBipartiteGraph(3,3))
            sphinx_plot(G.NAC_colorings()[4])

        ``col2``:

        .. PLOT::

            from rigid_and_flexible_graphs.rigid_flexible_graph import RigidFlexibleGraph
            from rigid_and_flexible_graphs.NAC_coloring import NACcoloring
            G = RigidFlexibleGraph(graphs.CompleteBipartiteGraph(3,3))
            sphinx_plot(G.NAC_colorings()[5])
        """
        if check and self._graph != other_coloring._graph:
            raise exceptions.RuntimeError('The NAC-colorings must belong to the same graph.')

        if aut_group==None:
            aut_group = self._graph.automorphism_group()
        if (Set([len(self.blue_edges()), len(self.red_edges())]) 
            != Set([len(other_coloring.blue_edges()), len(other_coloring.red_edges())])):
            if not certificate:
                return False
            else:
                return (False, None)

        for sigma in aut_group:
            if Set([self._red_edges, self._blue_edges]) == Set(other_coloring.isomorphic_NAC_coloring(sigma,onlySets=True)): # faster
            #if self.is_equal(other_coloring.isomorphic_NAC_coloring(sigma)):
                if not certificate:
                    return True
                else:
                    return (True, sigma)
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

            sage: from rigid_and_flexible_graphs.NAC_coloring import NACcoloring
            sage: from rigid_and_flexible_graphs.graph_generator import GraphGenerator
            sage: G = GraphGenerator.SmallestFlexibleLamanGraph(); G
            SmallestFlexibleLamanGraph: RigidFlexibleGraph with the vertices [0, 1, 2, 3, 4] and edges [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 4), (3, 4)]
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

            sage: from rigid_and_flexible_graphs.graph_generator import GraphGenerator
            sage: G = GraphGenerator.SmallestFlexibleLamanGraph()
            sage: delta = G.NAC_colorings()[0]; delta
            NAC-coloring with red edges {{1, 3}, {1, 2}, {0, 2}, {0, 3}, {0, 1}} and blue edges {{2, 4}, {3, 4}}
            sage: delta.set_name('delta'); delta
            delta: NAC-coloring with red edges {{1, 3}, {1, 2}, {0, 2}, {0, 3}, {0, 1}} and blue edges {{2, 4}, {3, 4}}
            sage: latex(delta)
            \delta: \left( \left\{\left\{1, 3\right\},
            ...
            \left\{3, 4\right\}\right\} \mapsto blue\right)
        """
        self._name = new_name

    def path_is_unicolor(self, path):
        r"""
        Return if the edges of the path have the same color.
        """
        edges = Set([Set(e) for e in zip(path[:-1],path[1:])])
        return edges.issubset(self._red_edges) or edges.issubset(self._blue_edges)


    def grid_coordinates(self):
        r"""
        Return coordinates for the grid construction.

        See [GLS2018]_ for the description of the grid construction.
        """
        red_subgraph = Graph(self.red_edges(), format='list_of_edges')
        red_components = red_subgraph.connected_components()
        red_components += [[v] for v in Set(self._graph.vertices()).difference(Set(flatten(red_components)))]
        blue_subgraph = Graph(self.blue_edges(), format='list_of_edges')
        blue_components = blue_subgraph.connected_components()
        blue_components += [[v] for v in Set(self._graph.vertices()).difference(Set(flatten(blue_components)))]
        pos = {}
        for (i,red) in enumerate(red_components):
            for (j,blue) in enumerate(blue_components):
                for v in blue:
                    if v in red:
                        pos[v] = (i,j)
        return pos

    def grid_coordinates_are_injective(self):
        r"""
        Return if the grid coordinates are injective.

        EXAMPLES::

            sage: from rigid_and_flexible_graphs.graph_generator import GraphGenerator
            sage: G = GraphGenerator.ThreePrismGraph()
            sage: delta = G.NAC_colorings()[0]
            sage: delta.grid_coordinates_are_injective()
            True

        ::

            sage: from rigid_and_flexible_graphs.graph_generator import GraphGenerator
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







__doc__ = __doc__.replace(
    "{INDEX_OF_METHODS}", (gen_rest_table_index(NACcoloring)))
