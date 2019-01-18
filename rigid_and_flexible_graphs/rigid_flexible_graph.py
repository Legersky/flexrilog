# -*- coding: utf-8 -*-
r"""
Rigid and Flexible Graphs
=========================

This module implements functionality for investigating rigidity and flexibility of graphs.

The following notions from Rigidity Theory are used:

Let :math:`G=(V_G,E_G)` be a graph with an edge labeling $\\lambda:E_G\\rightarrow \\mathbb{R}_+$.

A realization $\\rho:V_G\\rightarrow\\mathbb{R}^2$ is called *compatible* with $\\lambda$ if
$||\\rho(u)-\\rho(v)||=\\lambda(uv)$ for all $uv\\in E_G$.

The labeling $\\lambda$ is called

- *(proper) flexible* if the number of (injective) realizations of $G$ compatible with $\\lambda$ is infinite,
- *rigid* if the number of realizations of $G$ compatible with $\\lambda$ is infinite,

where the counting is up to direct Euclidean isometries.

A graph is called *movable* iff it has a proper flexible labeling.

A graph is *generically rigid*, i.e., a generic realization defines a rigid labeling,
if and only if the graph contains a *Laman* subgraph with the same set of vertices [Lam1970]_, [Pol1927]_.

A graph $G=(V_G,E_G)$ is called *Laman* if $|E_G| = 2|V_G|-3$,
and $|E_H|\\leq 2|V_H|-3$ for all subgraphs $H$ of $G$,
see :wikipedia:`Wikipedia <Laman_graph>`. 

Methods
-------


{INDEX_OF_METHODS}

AUTHORS:

-  Jan Legerský (2019-01-15): initial version

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

from sage.all import Graph, Set, ceil, sqrt, matrix, deepcopy, copy
from sage.all import Subsets, SageObject
from sage.misc.rest_index_of_methods import doc_index, gen_thematic_rest_table_index
from sage.rings.integer import Integer
from sage.rings.rational import Rational

import exceptions


class RigidFlexibleGraph(Graph):
    r"""
    The class RigidFlexibleGraph is inherited from 
    `sage.graphs.graph.Graph <http://doc.sagemath.org/html/en/reference/graphs/sage/graphs/graph.html>`_.
    It is a simple undirected connected graph with at least one edge.
    It adds functionality for rigidity and flexibility of the graph.
    For the definition of a graph, see 
    :wikipedia:`Wikipedia <Graph_(mathematics)>`.

    INPUT:

    - ``data``: provides the information about edges. There are three possibilities:

      * ``RigidFlexibleGraph(list_of_edges)`` -- return the graph with the edges given by ``list_of_edges``.
      * ``RigidFlexibleGraph(number)`` -- build a graph whose adjacence matrix is given as follows: 
        the binary expansion of the integer ``number`` is written row by row into the upper triangle, 
        excluding the diagonal, and symmetrically also into the lower triangle.
      * ``RigidFlexibleGraph(graph)`` -- return the graph with the same edges, positions and name as ``graph``.

    - ``name`` --  gives the graph a name 
    - ``pos`` -- a positioning dictionary. For example, to
      draw 4 vertices on a square ``pos={0: [-1,-1], 1: [ 1,-1], 2: [ 1, 1], 3: [-1, 1]}``.
    - ``check`` (boolen) -- If ``True`` (default), then it is checked whether the graph connected and has at least one edge.

    EXAMPLES:

        The single edge graph::

            from rigid_and_flexible_graphs.rigid_flexible_graph import RigidFlexibleGraph
            sage: G = RigidFlexibleGraph(1); G
            RigidFlexibleGraph with the vertices [0, 1] and edges [(0, 1)]

        Graphs without edges are not allowed::

            sage: G = RigidFlexibleGraph([]); G
            Traceback (most recent call last):
            ...
            ValueError: The graph must have at least one edge.

        A named graph given by integer represenation with specified positions::

            sage: G = RigidFlexibleGraph(7916, name='3-prism', 
            ....:       pos={0: [0.6, 0.4], 1: [0, 1.4], 2: [1, 1.4],
            ....:            3: [1, 0], 4: [0, 0], 5: [0.6, 1]}); G
            3-prism: RigidFlexibleGraph with the vertices [0, 1, 2, 3, 4, 5] and edges [(0, 3), (0, 4), (0, 5), (1, 2), (1, 4), (1, 5), (2, 3), (2, 5), (3, 4)]
            sage: from rigid_and_flexible_graphs.graph_generator import GraphGenerator
            sage: G == GraphGenerator.ThreePrismGraph()
            True

        The dictionary ``pos`` is used when plotting:

        .. PLOT::

            from rigid_and_flexible_graphs.graph_generator import GraphGenerator
            G = GraphGenerator.ThreePrismGraph()
            sphinx_plot(G)

        The 3-cycle graph given by the list of edges::

            sage: G = RigidFlexibleGraph([[0,1],[1,2],[0,2]], name='3-cycle'); G
            3-cycle: RigidFlexibleGraph with the vertices [0, 1, 2] and edges [(0, 1), (0, 2), (1, 2)]

        An instance of `sage.graphs.graph.Graph <http://doc.sagemath.org/html/en/reference/graphs/sage/graphs/graph.html>`_
        can be used::

            sage: L = RigidFlexibleGraph(graphs.CompleteBipartiteGraph(2,3)); L
            Complete bipartite graph: RigidFlexibleGraph with the vertices [0, 1, 2, 3, 4] and edges [(0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4)]

    """

    def __init__(self, data, pos=None, name=None, check=True):
        if type(data)==Integer:
            edges = self._int2graph_edges(data)
        elif type(data)==list:
            edges = data
        elif type(data)==Graph:
            edges = data.edges()
            pos = data.get_pos()
            if data.name():
                name = data.name()
        else:
            raise exceptions.TypeError('The input must be an integer or a list of edges.')

        if pos==None:
            tmp_g=Graph(data=[[e[0],e[1]] for e in edges], format='list_of_edges')
            tmp_g.graphplot(save_pos=True)
            pos = tmp_g.get_pos()

        Graph.__init__(self,data=[[e[0],e[1]] for e in edges], format='list_of_edges',
                       name=name, pos=pos, loops=False, multiedges=False)

        if check:
            if not self.is_connected():
                raise exceptions.ValueError('The graph must be connected.')
            if len(self.edges())==0:
                raise exceptions.ValueError('The graph must have at least one edge.')

        self._triangleComponents = None
        self._NACs_computed = 'no'

    def _repr_(self):
        if self.name():
            pref = self.name() +': '
        else:
            pref = ''
        if len(self.edges(labels=False)) < 10:
            return (pref + 'RigidFlexibleGraph with the vertices '+str(self.vertices()) + 
                    ' and edges '+str(self.edges(labels=False)) + '')
        else:
            return (pref + 'RigidFlexibleGraph with ' +str(len(self.vertices())) + 
                    ' vertices and ' + str(len(self.edges(labels=False))) + ' edges') 


    def __copy__(self):
        cls = self.__class__
        result = cls.__new__(cls)
        result.__dict__.update(self.__dict__)
        return result


    def __deepcopy__(self, memo):
        cls = self.__class__
        result = cls.__new__(cls)
        memo[id(self)] = result
        for k, v in self.__dict__.items():
            setattr(result, k, deepcopy(v, memo))
        return result


    def _int2graph_edges(self,N):
        r"""
        Return edges of the graph with integer represenation ``N``.

        The integer represenation works as follows: 
        the binary expansion of ``N`` equals the sequence
        obtained by concatenation of the rows of the upper triangle of the adjacency matrix,
        excluding the diagonal.
        """
        L=Integer(N).binary()
        n=ceil((1+sqrt(1+8*len(L)))/Integer(2))
        adjacencyMatrix=matrix(n,n)
        j=len(L)
        r=n-1
        c=n-1
        row_len=n-1
        while j>0:
            c+=-1
            if c<=row_len:
                row_len+=-1
                c=n-1
                r+=-1
            j-=1
            adjacencyMatrix[r,c]=L[j]
        return Graph(adjacencyMatrix+adjacencyMatrix.transpose()).edges(labels=False)


    @doc_index("Other")
    def graph2int(self, canonical=True):
        r"""
        Return the integer representation of the graph.

        The graph has integer represenation `N`
        if the binary expansion of ``N`` equals the sequence
        obtained by concatenation of the rows of the upper triangle of the adjacency matrix,
        excluding the diagonal.

        INPUT:

        - ``canonical`` (boolean) -- if ``True`` (default),
          then the adjacency matrix of the isomorphic graph
          obtained by `canonical_label() 
          <http://doc.sagemath.org/html/en/reference/graphs/sage/graphs/generic_graph.html#sage.graphs.generic_graph.GenericGraph.canonical_label>`_
          is used. In this case, the isomorphic graphs have the same integer representation.

        EXAMPLES::

            sage: G = RigidFlexibleGraph(graphs.CycleGraph(4)); G
            Cycle graph: RigidFlexibleGraph with the vertices [0, 1, 2, 3] and edges [(0, 1), (0, 3), (1, 2), (2, 3)]
            sage: G.graph2int(canonical=False)
            45
            sage: G.adjacency_matrix()
            [0 1 0 1]
            [1 0 1 0]
            [0 1 0 1]
            [1 0 1 0]
            sage: int('101101',2)
            45
            sage: G.graph2int()
            30
            sage: H = RigidFlexibleGraph(30); H
            RigidFlexibleGraph with the vertices [0, 1, 2, 3] and edges [(0, 2), (0, 3), (1, 2), (1, 3)]
            sage: H.graph2int()
            30
        """
        if canonical:
            M= Graph(self.edges(labels=False)).canonical_label().adjacency_matrix()
        else:
            M= self.adjacency_matrix()
        return Integer(int(''.join([str(b) for i,row in enumerate(M) for b in row[i+1:]]),2))


    @doc_index("Rigidity")
    def is_Laman(self, algorithm=None, certificate=False):
        r"""
        Return whether the graph is Laman.

        A graph $G=(V_G,E_G)$ is called *Laman* if $|E_G| = 2|V_G|-3$,
        and $|E_H|\\leq 2|V_H|-3$ for all subgraphs $H$ of $G$,
        see :wikipedia:`Wikipedia <Laman_graph>`. 

        INPUT:

        - ``algorithm`` (string) -- there are two options:

          * If ``algorithm = "definition"``, then the Laman condition on subgraphs is checked naively (VERY SLOW!!).
          * If ``algorithm = "Henneberg"`` (default), then a sequence of Henneberg steps is attempted to be found (SLOW!!).

        - ``certificate`` (boolean) -- If ``certificate = False`` (default),
          then the returns only boolean. Otherwise:

          * If ``algorithm = "Henneberg"``, then
            it either answers ``(True, s)`` when the graph is Laman and can be constructed by Henneberg sequence ``s``, or ``(False, None)`` 
            when it is not Laman. See :meth:`Henneberg_sequence`.
          * If ``algorithm = "definition"``, then the certificate is ``None`` if
            the graph is Laman, otherwise ``(False, H)``, where ``H`` is the graph
            that violates the condition.

        EXAMPLES:

        3-prism is Laman::

            sage: from rigid_and_flexible_graphs.graph_generator import GraphGenerator
            sage: G = GraphGenerator.ThreePrismGraph()
            sage: G.is_Laman()
            True
            sage: G.is_Laman(certificate=True)
            (True, [('II', 0, (3, 5)), ('I', 4), ('I', 1), ('I', 2)])
            sage: G.is_Laman(algorithm='definition')
            True

        4-cycle is not Laman::

            sage: G = RigidFlexibleGraph([[0,1],[1,2],[2,3],[0,3]])
            sage: G.is_Laman(algorithm='definition', certificate=True)
            (False, Graph on 4 vertices)
            sage: G.is_Laman(algorithm='Henneberg', certificate=True)
            (False, None)

        The complete graph $K_4$ is not Laman::

            sage: G = RigidFlexibleGraph([(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)])
            sage: G.is_Laman(algorithm='definition', certificate=True)
            (False, Graph on 4 vertices)
            sage: G.is_Laman(algorithm='Henneberg', certificate=True)
            (False, None)

        TODO:

        Implementation of pebble game algorithm.
        
        """
        if algorithm==None:
            algorithm = "Henneberg"

        if algorithm=="definition":
            if len(self.edges())!=2*len(self.vertices())-3:
                if certificate:
                    return (False, Graph(self))
                else:
                    return False
            for k in range(4,len(self.vertices())):
                for subvert in Subsets(self.vertices(),k):
                    g_ind=Graph(self).subgraph(subvert.list())
                    if len(g_ind.edges())>2*len(g_ind.vertices())-3:
                        if certificate:
                            return (False, g_ind)
                        else:
                            return False
            if certificate:
                return (True, None)
            else:
                return True
        elif algorithm=="Henneberg":
            s = self.Henneberg_sequence()
            if certificate:
                return (s!=None, s)
            else:
                return s!=None
        else:
            raise exceptions.ValueError('The algorithm ' + str(algorithm) 
                                        + ' is not supported')


    @doc_index("Rigidity")
    def _inverse_Henneberg_step(self, g, seq, onlyOne):
        r"""
        Undo Henneberg steps recursively. 

        If ``onlyOne==True``, then only one sequence is searched.
        """
        if self._Henneberg_sequences and onlyOne:
            return

        degTwo=[v for v in g.vertices() if g.degree(v)==2]
        if onlyOne and degTwo:
            degTwo = [degTwo[0]]
        for v in degTwo:
            g_smaller = deepcopy(g)
            g_smaller.delete_vertex(v)
            self._inverse_Henneberg_step(g_smaller, seq+[('I',degTwo[0])], onlyOne)
        degThree = [v for v in g.vertices() if g.degree(v)==3]
        for v in degThree:
            [u1,u2,u3] = g.neighbors(v)
            g_smaller = deepcopy(g)
            g_smaller.delete_vertex(v)
            if not g.has_edge(u1,u2):
                g_smaller.add_edge(u1,u2)
                self._inverse_Henneberg_step(g_smaller, seq+[('II',v, (u1,u2))], onlyOne)
            if not g.has_edge(u1,u3):
                g_smaller.add_edge(u1,u3)
                self._inverse_Henneberg_step(g_smaller, seq+[('II',v, (u1,u3))], onlyOne)
            if not g.has_edge(u3,u2):
                g_smaller.add_edge(u3,u2)
                self._inverse_Henneberg_step(g_smaller, seq+[('II',v, (u3,u2))], onlyOne)
        if len(g.edges())==1 and len(g.vertices())==2:
            if onlyOne:
                self._Henneberg_sequences.append(seq)
                return seq
            else:
                self._Henneberg_sequences.append(seq)


    @doc_index("Rigidity")
    def Henneberg_sequence(self, onlyOne=True):
        r"""
        Return Henneberg sequence(s) of the graph.

        The graph is Laman if and only if it can be constructed 
        using Henneberg steps, see :wikipedia:`Wikipedia <Laman_graph#Henneberg_construction>`.

        INPUT:

        - ``onlyOne`` -- if ``True`` (default),
          then only one Henneberg sequence is returned (if exists).
          Otherwise, all sequences are found.

        OUTPUT:

        The sequence is reversed - it describes the order of removing vertices
        by undoing Henneberg steps : ``('I',u)`` denotes that the vertex ``u``
        of degree two is removed and ``('II', u, (v, w))`` means that the vertex
        ``u`` of degree three is removed and the edge ``[v, w]`` is added.
        If there is no Henneberg sequence, then the output is ``None``.

        EXAMPLES:

        A Henneberg sequence for 3-prism::

            sage: G = RigidFlexibleGraph(7916); G
            RigidFlexibleGraph with the vertices [0, 1, 2, 3, 4, 5] and edges [(0, 3), (0, 4), (0, 5), (1, 2), (1, 4), (1, 5), (2, 3), (2, 5), (3, 4)]
            sage: print G.Henneberg_sequence()
            [('II', 0, (3, 5)), ('I', 4), ('I', 1), ('I', 2)]

        4-cycle is not Laman::

            sage: G = RigidFlexibleGraph([[0,1],[1,2],[2,3],[0,3]])
            sage: G.Henneberg_sequence()==None
            True

        The complete graph $K_4$ is not Laman::

            sage: G = RigidFlexibleGraph([(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)])
            sage: G.Henneberg_sequence()==None
            True

        All Henneberg sequence of $K_4$ with one edge removed::

            sage: G = RigidFlexibleGraph([[0,1],[1,2],[2,3],[0,3],[0,2]])
            sage: G.Henneberg_sequence()
            [('I', 1), ('I', 0)]
            sage: G.Henneberg_sequence(onlyOne=False)
            [[('I', 1), ('I', 0)],
            [('I', 1), ('I', 0)],
            [('I', 1), ('I', 0)],
            [('I', 1), ('I', 0)],
            [('I', 1), ('I', 0)],
            [('I', 1), ('I', 0)],
            [('II', 0, (1, 3)), ('I', 1)],
            [('II', 0, (1, 3)), ('I', 1)],
            [('II', 0, (1, 3)), ('I', 1)],
            [('II', 2, (3, 1)), ('I', 0)],
            [('II', 2, (3, 1)), ('I', 0)],
            [('II', 2, (3, 1)), ('I', 0)]]

        """
        self._Henneberg_sequences=[]
        if onlyOne:
            self._inverse_Henneberg_step(self, [], True)
            if self._Henneberg_sequences:
                return self._Henneberg_sequences[0]
            else:
                return None
        else:
            self._inverse_Henneberg_step(self, [], False)
            if self._Henneberg_sequences:
                res = copy(self._Henneberg_sequences)
                self._Henneberg_sequences = None
                return res
            else:
                return None


    @doc_index("Rigidity")
    def Henneberg_sequence2graphs(self, seq):
        r"""
        Return graphs of Henneberg sequence.

        INPUT:

        - ``seq`` - sequence of Henneberg steps as outputted 
          by :meth:`Henneberg_sequence`.

        OUTPUT:

        Graphs obtained by applying the Henneberg sequence ``seq``.

        EXAMPLE::

            sage: from rigid_and_flexible_graphs.graph_generator import GraphGenerator
            sage: G = GraphGenerator.ThreePrismGraph()
            sage: seq = G.Henneberg_sequence(); seq
            [('II', 0, (3, 5)), ('I', 4), ('I', 1), ('I', 2)]
            sage: G.Henneberg_sequence2graphs(seq)
            [3-prism: Graph on 2 vertices,
            3-prism: Graph on 3 vertices,
            3-prism: Graph on 4 vertices,
            3-prism: Graph on 5 vertices,
            3-prism: Graph on 6 vertices]

        """
        graph_seq = [Graph(deepcopy(self))]
        for step in seq:
            g_smaller=deepcopy(graph_seq[-1])
            if step[0]=='I':
                g_smaller.delete_vertex(step[1])
            elif step[0]=='II':
                g_smaller.delete_vertex(step[1])
                g_smaller.add_edge(step[2][0],step[2][1])
            graph_seq.append(g_smaller)
        return list(reversed(graph_seq))


    @doc_index("Graph properties")
    def triangle_connected_components(self):
        r"""
        Return triangle connected components.

        Two edges are in relation if they are in the same 3-cycle subgraph.
        The eqiuvalence classes of the reflexive-transitive closure
        of this relation are called $\\triangle$-connected components [GLS2018]_.

        OUTPUT:

        Partition of the edges into the $\\triangle$-connected components.

        EXAMPLE::

            sage: G = RigidFlexibleGraph([(1,6),(2,6),(0,6),(0, 3), (0, 4), 
            ....: (0, 5), (1, 2), (1, 4), (1, 5), (2, 3), (2, 5), (3, 4)]); G
            RigidFlexibleGraph with 7 vertices and 12 edges
            sage: G.triangle_connected_components()
            [[[0, 3], [0, 4], [3, 4]], [[1, 2], [1, 5], [1, 6], [2, 5], [2, 6]], [[0, 5]], [[0, 6]], [[1, 4]], [[2, 3]]]

        ::

            sage: from rigid_and_flexible_graphs.graph_generator import GraphGenerator
            sage: G = GraphGenerator.ThreePrismGraph()
            sage: G.triangle_connected_components()
            [[[0, 3], [0, 4], [3, 4]], [[1, 2], [1, 5], [2, 5]], [[0, 5]], [[1, 4]], [[2, 3]]]

        WARNING:

        Labels of edges are modified during the computation.

        TODO:

        Change so that the edge labels are not used.
        """

        def addToTrComp(u0,u1,n_tr):
            if self.edge_label(u0,u1)==None:
                self.set_edge_label(u0,u1,n_tr)
                common_neighbours=Set(
                    self.neighbors(u0)).intersection(Set(self.neighbors(u1)))
                if common_neighbours:
                    for u in common_neighbours:
                        addToTrComp(u0,u,n_tr)
                        addToTrComp(u,u1,n_tr)
                    return 'trcomp'
                else:
                    self.set_edge_label(u0,u1,'c')
                    return 'connectingEdge'

        for e in self.edges():
            self.set_edge_label(e[0],e[1],None)

        n_tr = 0
        e = self.edges()[0]
        while e[2]==None:
            res = addToTrComp(e[0],e[1],n_tr)
            e = self.edges(key=lambda x: x[2])[0]
            if res=='trcomp':
                n_tr += 1

        triangleComponents = [[] for _ in xrange(0,n_tr)]
        for u,v,l in self.edges():
            if l == 'c':
                triangleComponents.append([[u,v]])
            else:
                triangleComponents[l].append([u,v])
        return triangleComponents

    @doc_index("Flexibility")
    def _find_NAC_colorings(self,onlyOne=False):
        r"""
        Find NAC-colorings of the graph and store them.

        The method finds NAC-colorings of the graph and store them in ``self._NAC_colorings``.
        The flag ``self._NACs_computed`` is changed to ``'yes'`` or ``'onlyOne'``.
        """
        triangle_comps = self.triangle_connected_components()
        n = len(triangle_comps)
        form_len = '0'+str(n-1)+'b'
        self._NAC_colorings = []

        for i in range(1,Integer(2)**(n-1)):
            str_col = '0' + format(i,form_len)
            red = []
            blue = []
            for i, comp in enumerate(triangle_comps):
                if str_col[i] == '0':
                    red += comp
                else:
                    blue += comp
            col = NACcoloring(self, [red, blue], check=False)
            if col.is_NACcoloring():
                self._NAC_colorings.append(col)
                if onlyOne:
                    self._NACs_computed = 'onlyOne'
                    return 
        self._NACs_computed = 'yes'

    @doc_index("Flexibility")
    def NAC_colorings(self):
        r"""
        Return NAC-colorings of the graph.

        If the NAC-colorings are already stored,
        then they are just returned, otherwise computed.

        EXAMPLES::

            sage: from rigid_and_flexible_graphs.graph_generator import GraphGenerator
            sage: G = GraphGenerator.ThreePrismGraph()
            sage: G.NAC_colorings()
            [NAC-coloring with red edges {{3, 4}, {2, 5}, {1, 2}, {1, 5}, {0, 4}, {0, 3}} and blue edges {{0, 5}, {2, 3}, {1, 4}}]

        ::

            sage: from rigid_and_flexible_graphs.rigid_flexible_graph import RigidFlexibleGraph
            sage: K = RigidFlexibleGraph(graphs.CompleteGraph(4))
            sage: K.NAC_colorings()
            []

        ::

            sage: K = RigidFlexibleGraph(graphs.CompleteBipartiteGraph(3,3))
            sage: len(K.NAC_colorings())
            15

        The NAC-colorings are cached::

            sage: K = RigidFlexibleGraph(graphs.CompleteBipartiteGraph(3,3))
            sage: %time len(K.NAC_colorings()) # doctest: +SKIP
            CPU times: user 418 ms, sys: 22.4 ms, total: 440 ms
            Wall time: 411 ms
            15
            sage: %time len(K.NAC_colorings()) # doctest: +SKIP
            CPU times: user 36 µs, sys: 3 µs, total: 39 µs
            Wall time: 55.1 µs
            15

        """
        if self._NACs_computed != 'yes':
            self._find_NAC_colorings()
        return self._NAC_colorings


    @doc_index("Flexibility")
    def has_NAC_coloring(self, certificate=False):
        r"""
        Return if the graph has a NAC-coloring.

        INPUT:

        - ``certificate`` (boolean) -- if ``False`` (default),
          then only boolean value is returned.
          Otherwise, the output is ``(True, NACcoloring)`` or ``(False, None)``.

        EXAMPLES::

            sage: from rigid_and_flexible_graphs.graph_generator import GraphGenerator
            sage: G = GraphGenerator.ThreePrismGraph()
            sage: G.has_NAC_coloring()
            True
            sage: G.has_NAC_coloring(certificate=True)
            (True, NAC-coloring with red edges {{3, 4}, {2, 5}, {1, 2}, {1, 5}, {0, 4}, {0, 3}} and blue edges {{0, 5}, {2, 3}, {1, 4}})

        ::

            sage: from rigid_and_flexible_graphs.rigid_flexible_graph import RigidFlexibleGraph
            sage: K = RigidFlexibleGraph(graphs.CompleteGraph(4))
            sage: K.has_NAC_coloring()
            False
            sage: K.has_NAC_coloring(certificate=True)
            (False, None)

        ::

            sage: K = RigidFlexibleGraph(graphs.CompleteBipartiteGraph(3,3))
            sage: K.has_NAC_coloring(certificate=True)
            (True, NAC-coloring with red edges {{0, 5}, {1, 3}, {1, 5}, {1, 4}, {0, 4}, {0, 3}} and blue edges {{2, 4}, {2, 3}, {2, 5}})
        """
        if self._NACs_computed == 'no':
            self._find_NAC_colorings(onlyOne=True)
        if certificate:
            return (self._NAC_colorings!=[], self._NAC_colorings[0] if self._NAC_colorings!=[] else None)
        else:
            return self._NAC_colorings!=[]


    @doc_index("Flexibility")
    def has_flexible_labeling(self, certificate=False):
        r"""
        Alias for :meth:`has_NAC_coloring`.

        A flexible labeling exists if and only if a NAC-coloring exists (Theorem 3.1 in [GLS2018]_).
        """
        return self.has_NAC_coloring(certificate=certificate)


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

        sage: from rigid_and_flexible_graphs.rigid_flexible_graph import NACcoloring
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

            sage: from rigid_and_flexible_graphs.rigid_flexible_graph import NACcoloring
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

__doc__ = __doc__.replace(
    "{INDEX_OF_METHODS}",gen_thematic_rest_table_index(RigidFlexibleGraph))
























