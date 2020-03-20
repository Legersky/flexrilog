# -*- coding: utf-8 -*-
r"""
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

**FlexRiGraph**

{INDEX_OF_METHODS_FLEXRIGRAPH}

AUTHORS:

-  Jan Legerský (2019-01-15): initial version
-  Jan Legerský (2020-03-12): update to SageMath 9.0

TODO:

    - missing documentation of methods
    - PyPI repository
    - missing doctests in methods
    - tutorial notebooks (basics, flexibility, classification, animations...)
    - improve the quality of pictures in the documentation


FlexRiGraph
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

class FlexRiGraph(Graph):
    r"""
    The class FlexRiGraph is inherited from
    `sage.graphs.graph.Graph <http://doc.sagemath.org/html/en/reference/graphs/sage/graphs/graph.html>`_.
    It is a simple undirected connected graph with at least one edge.
    It adds functionality for rigidity and flexibility of the graph.
    The graph is immutable in order to prevent adding/removing edges or vertices.

    INPUT:

    - ``data``: provides the information about edges. There are three possibilities:

      * ``FlexRiGraph(list_of_edges)`` -- return the graph with the edges given by ``list_of_edges``.
      * ``FlexRiGraph(number)`` -- build a graph whose adjacence matrix is given as follows:
        the binary expansion of the integer ``number`` is written row by row into the upper triangle,
        excluding the diagonal, and symmetrically also into the lower triangle.
      * ``FlexRiGraph(graph)`` -- return the graph with the same edges, positions and name as ``graph``.

    - ``name`` --  gives the graph a name
    - ``pos`` -- a positioning dictionary. For example, to
      draw 4 vertices on a square ``pos={0: [-1,-1], 1: [ 1,-1], 2: [ 1, 1], 3: [-1, 1]}``.
    - ``check`` (boolean) -- If ``True`` (default), then it is checked whether the graph connected and has at least one edge.

    EXAMPLES:

        The single edge graph::

            sage: from flexrilog import FlexRiGraph
            sage: G = FlexRiGraph(1); G
            FlexRiGraph with the vertices [0, 1] and edges [(0, 1)]

        Graphs without edges are not allowed::

            sage: G = FlexRiGraph([]); G
            Traceback (most recent call last):
            ...
            ValueError: The graph must have at least one edge.

        A named graph given by integer representation with specified positions::

            sage: G = FlexRiGraph(7916, name='3-prism',
            ....:       pos={0: [0.6, 0.4], 1: [0, 1.4], 2: [1, 1.4],
            ....:            3: [1, 0], 4: [0, 0], 5: [0.6, 1]}); G
            3-prism: FlexRiGraph with the vertices [0, 1, 2, 3, 4, 5] and edges [(0, 3), (0, 4), (0, 5), (1, 2), (1, 4), (1, 5), (2, 3), (2, 5), (3, 4)]
            sage: from flexrilog import GraphGenerator
            sage: G == GraphGenerator.ThreePrismGraph()
            True

        The dictionary ``pos`` is used when plotting:

        .. PLOT::
            :width: 70%

            from flexrilog import GraphGenerator
            G = GraphGenerator.ThreePrismGraph()
            sphinx_plot(G)

        The 3-cycle graph given by the list of edges::

            sage: G = FlexRiGraph([[0,1],[1,2],[0,2]], name='3-cycle'); G
            3-cycle: FlexRiGraph with the vertices [0, 1, 2] and edges [(0, 1), (0, 2), (1, 2)]

        An instance of `sage.graphs.graph.Graph <http://doc.sagemath.org/html/en/reference/graphs/sage/graphs/graph.html>`_
        can be used::

            sage: L = FlexRiGraph(graphs.CompleteBipartiteGraph(2,3)); L
            Complete bipartite graph of order 2+3: FlexRiGraph with the vertices [0, 1, 2, 3, 4] and edges [(0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4)]

    TODO:
    
        Other inputs: adjacency matrix
    """

    def __init__(self, data, pos=None, name=None, check=True):
        if type(data)==Integer:
            edges = self._int2graph_edges(data)
        elif type(data)==list:
            edges = data
        elif isinstance(data, Graph):
            edges = data.edges()
            pos = data.get_pos()
            if data.name():
                name = data.name()
        else:
            raise TypeError('The input must be an integer or a list of edges.')

        if pos==None:
            tmp_g=Graph(data=[[e[0],e[1]] for e in edges], format='list_of_edges')
            tmp_g.graphplot(save_pos=True)
            pos = tmp_g.get_pos()

        Graph.__init__(self,data=[[e[0],e[1]] for e in edges], format='list_of_edges',
                       name=name, pos=pos, loops=False, multiedges=False, immutable=True)

        if check:
            if not self.is_connected():
                raise ValueError('The graph must be connected.')
            if len(self.edges())==0:
                raise ValueError('The graph must have at least one edge.')

        self._triangleComponents = None
        self._NACs_computed = 'no'
        self._NAC_isomorphism_classes = None

    def _repr_(self):
        if self.name():
            pref = self.name() +': '
        else:
            pref = ''
        pref += self.__class__.__name__
        if len(self.edges(labels=False)) < 10:
            return (pref + ' with the vertices '+str(self.vertices()) +
                    ' and edges '+str(self.edges(labels=False)) + '')
        else:
            return (pref + ' with ' +str(len(self.vertices())) +
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
        Return edges of the graph with integer representation ``N``.

        The integer representation works as follows:
        the binary expansion of ``N`` equals the sequence
        obtained by concatenation of the rows of the upper triangle of the adjacency matrix,
        excluding the diagonal.
        
        TODO: 
        
            change to static?
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

        The graph has integer representation `N`
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

            sage: from flexrilog import FlexRiGraph
            sage: G = FlexRiGraph(graphs.CycleGraph(4)); G
            Cycle graph: FlexRiGraph with the vertices [0, 1, 2, 3] and edges [(0, 1), (0, 3), (1, 2), (2, 3)]
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
            sage: H = FlexRiGraph(30); H
            FlexRiGraph with the vertices [0, 1, 2, 3] and edges [(0, 2), (0, 3), (1, 2), (1, 3)]
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

            sage: from flexrilog import GraphGenerator
            sage: G = GraphGenerator.ThreePrismGraph()
            sage: G.is_Laman()
            True
            sage: G.is_Laman(certificate=True)
            (True, [('II', 0, (3, 5)), ('I', 4), ('I', 1), ('I', 2)])
            sage: G.is_Laman(algorithm='definition')
            True

        4-cycle is not Laman::

            sage: from flexrilog import FlexRiGraph
            sage: G = FlexRiGraph([[0,1],[1,2],[2,3],[0,3]])
            sage: G.is_Laman(algorithm='definition', certificate=True)
            (False, Graph on 4 vertices)
            sage: G.is_Laman(algorithm='Henneberg', certificate=True)
            (False, None)

        The complete graph $K_4$ is not Laman::

            sage: G = FlexRiGraph([(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)])
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
            if len(self.edges())!=2*len(self.vertices())-3:
                if certificate:
                    return (False, None)
                else:
                    return False
            s = self.Henneberg_sequence()
            if certificate:
                return (s!=None, s)
            else:
                return s!=None
        else:
            raise ValueError('The algorithm ' + str(algorithm)
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

            sage: from flexrilog import FlexRiGraph
            sage: G = FlexRiGraph(7916); G
            FlexRiGraph with the vertices [0, 1, 2, 3, 4, 5] and edges [(0, 3), (0, 4), (0, 5), (1, 2), (1, 4), (1, 5), (2, 3), (2, 5), (3, 4)]
            sage: print(G.Henneberg_sequence())
            [('II', 0, (3, 5)), ('I', 4), ('I', 1), ('I', 2)]

        4-cycle is not Laman::

            sage: G = FlexRiGraph([[0,1],[1,2],[2,3],[0,3]])
            sage: G.Henneberg_sequence()==None
            True

        The complete graph $K_4$ is not Laman::

            sage: G = FlexRiGraph([(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)])
            sage: G.Henneberg_sequence()==None
            True

        All Henneberg sequence of $K_4$ with one edge removed::

            sage: G = FlexRiGraph([[0,1],[1,2],[2,3],[0,3],[0,2]])
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

            sage: from flexrilog import GraphGenerator
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
    def is_complete(self):
        r"""
        Return if the graph is complete.
        """
        return self.num_edges() == binomial(self.num_verts(),2)


    @doc_index("Graph properties")
    def triangle_connected_components(self):
        r"""
        Return triangle connected components.

        Two edges are in relation if they are in the same 3-cycle subgraph.
        The equivalence classes of the reflexive-transitive closure
        of this relation are called $\\triangle$-connected components [GLS2018]_.

        OUTPUT:

        Partition of the edges into the $\\triangle$-connected components.

        EXAMPLE::

            sage: from flexrilog import FlexRiGraph
            sage: G = FlexRiGraph([(1,6),(2,6),(0,6),(0, 3), (0, 4),
            ....: (0, 5), (1, 2), (1, 4), (1, 5), (2, 3), (2, 5), (3, 4)]); G
            FlexRiGraph with 7 vertices and 12 edges
            sage: G.triangle_connected_components()
            [[[0, 3], [0, 4], [3, 4]], [[1, 2], [1, 5], [1, 6], [2, 5], [2, 6]], [[0, 5]], [[0, 6]], [[1, 4]], [[2, 3]]]

        ::

            sage: from flexrilog import GraphGenerator
            sage: G = GraphGenerator.ThreePrismGraph()
            sage: G.triangle_connected_components()
            [[[0, 3], [0, 4], [3, 4]], [[1, 2], [1, 5], [2, 5]], [[0, 5]], [[1, 4]], [[2, 3]]]

        TODO:

        Change so that the edge labels are not used (without creating extra copy).
        """
        G = Graph(self.edges(labels=False))

        def addToTrComp(u0,u1,n_tr):
            if G.edge_label(u0,u1)==-2:
                G.set_edge_label(u0,u1,n_tr)
                common_neighbours=Set(
                    G.neighbors(u0)).intersection(Set(G.neighbors(u1)))
                if common_neighbours:
                    for u in common_neighbours:
                        addToTrComp(u0,u,n_tr)
                        addToTrComp(u,u1,n_tr)
                    return 'trcomp'
                else:
                    G.set_edge_label(u0,u1,-1)
                    return 'connectingEdge'

        for e in G.edges():
            G.set_edge_label(e[0],e[1],-2)

        n_tr = 0
        e = G.edges()[0]
        while e[2]==-2:
            res = addToTrComp(e[0],e[1],n_tr)
            e = G.edges(key=lambda x: x[2])[0]
            if res=='trcomp':
                n_tr += 1

        triangleComponents = [[] for _ in range(0,n_tr)]
        for u,v,l in G.edges():
            if l == -1:
                triangleComponents.append([[u,v]])
            else:
                triangleComponents[l].append([u,v])
        return triangleComponents
    
    @doc_index("NAC-colorings")
    def _edges_with_same_color(self):
        return self.triangle_connected_components()

    @doc_index("NAC-colorings")
    def _find_NAC_colorings(self, onlyOne=False, names=False):
        r"""
        Find NAC-colorings of the graph and store them.

        The method finds NAC-colorings of the graph and store them in ``self._NAC_colorings``.
        The flag ``self._NACs_computed`` is changed to ``'yes'`` or ``'onlyOne'``.
        
        TODO:
        
         - skip testing combinations that fail on a subgraph 
        """
        triangle_comps = self._edges_with_same_color()
        n = len(triangle_comps)
        form_len = '0'+str(n-1)+'b'
        self._NAC_colorings = []

        counter = 1
        for i in range(1,Integer(2)**(n-1)):
            str_col = '0' + format(i,form_len)
            red = []
            blue = []
            for i, comp in enumerate(triangle_comps):
                if str_col[i] == '0':
                    red += comp
                else:
                    blue += comp
            if names:
                col = NACcoloring(self, [red, blue], check=False, name='delta_' + str(counter))
            else:
                col = NACcoloring(self, [red, blue], check=False)
            if col.is_NAC_coloring():
                self._NAC_colorings.append(col)
                counter += 1
                if onlyOne:
                    self._NACs_computed = 'onlyOne'
                    return
        self._NACs_computed = 'yes'

    @doc_index("NAC-colorings")
    def NAC_colorings(self):
        r"""
        Return NAC-colorings of the graph.

        If the NAC-colorings are already stored,
        then they are just returned, otherwise computed.

        OUTPUT:

        Only one NAC-coloring per conjugacy class is return.

        EXAMPLES::

            sage: from flexrilog import GraphGenerator
            sage: G = GraphGenerator.ThreePrismGraph()
            sage: G.NAC_colorings()
            [NAC-coloring with red edges [[0, 3], [0, 4], [1, 2], [1, 5], [2, 5], [3, 4]] and blue edges [[0, 5], [1, 4], [2, 3]]]

        ::

            sage: from flexrilog import FlexRiGraph
            sage: K = FlexRiGraph(graphs.CompleteGraph(4))
            sage: K.NAC_colorings()
            []

        ::

            sage: K = FlexRiGraph(graphs.CompleteBipartiteGraph(3,3))
            sage: len(K.NAC_colorings())
            15

        The NAC-colorings are cached::

            sage: K = FlexRiGraph(graphs.CompleteBipartiteGraph(3,3))
            sage: %time len(K.NAC_colorings()) # doctest: +SKIP
            CPU times: user 418 ms, sys: 22.4 ms, total: 440 ms
            Wall time: 411 ms
            15
            sage: %time len(K.NAC_colorings()) # doctest: +SKIP
            CPU times: user 36 µs, sys: 3 µs, total: 39 µs
            Wall time: 55.1 µs
            15
        
        TODO:

            Implement as an iterator?
        """
        if self._NACs_computed != 'yes':
            self._find_NAC_colorings()
        return self._NAC_colorings


    @doc_index("NAC-colorings")
    def name2NAC_coloring(self, name):
        r"""
        Return the NAC-coloring with the given name.

        TODO:

        Implement using a dictionary instead of traversing the whole list each time.
        """
        for delta in self.NAC_colorings():
            if delta.name() == name:
                return delta
        return None

    @doc_index("NAC-colorings")
    def has_NAC_coloring(self, certificate=False):
        r"""
        Return if the graph has a NAC-coloring.

        INPUT:

        - ``certificate`` (boolean) -- if ``False`` (default),
          then only boolean value is returned.
          Otherwise, the output is ``(True, NACcoloring)`` or ``(False, None)``.

        EXAMPLES::

            sage: from flexrilog import GraphGenerator
            sage: G = GraphGenerator.ThreePrismGraph()
            sage: G.has_NAC_coloring()
            True
            sage: G.has_NAC_coloring(certificate=True)
            (True, NAC-coloring with red edges [[0, 3], [0, 4], [1, 2], [1, 5], [2, 5], [3, 4]] and blue edges [[0, 5], [1, 4], [2, 3]])
            
        ::

            sage: from flexrilog import FlexRiGraph
            sage: K = FlexRiGraph(graphs.CompleteGraph(4))
            sage: K.has_NAC_coloring()
            False
            sage: K.has_NAC_coloring(certificate=True)
            (False, None)

        ::

            sage: K = FlexRiGraph(graphs.CompleteBipartiteGraph(3,3))
            sage: K.has_NAC_coloring(certificate=True)
            (True, NAC-coloring with red edges [[0, 3], [0, 4], [0, 5], [1, 3], [1, 4], [1, 5]] and blue edges [[2, 3], [2, 4], [2, 5]])
        """
        if self._NACs_computed == 'no':
            self._find_NAC_colorings(onlyOne=True)
        if certificate:
            return (self._NAC_colorings!=[], self._NAC_colorings[0] if self._NAC_colorings!=[] else None)
        else:
            return self._NAC_colorings!=[]


    @doc_index("NAC-colorings")
    def has_flexible_labeling(self, certificate=False):
        r"""
        Alias for :meth:`has_NAC_coloring`.

        A flexible labeling exists if and only if a NAC-coloring exists (Theorem 3.1 in [GLS2018]_).
        """
        return self.has_NAC_coloring(certificate=certificate)


    @doc_index("Plotting")
    def plot(self, NAC_coloring=None, show_triangle_components=False, name_in_title=True, **kwargs):
        r"""
        Return the plot of the graph.

        INPUT:

        - ``NAC_coloring`` -- if an instance of :class:`NACcoloring` is provided,
          then the edges are colored accordingly.
        - ``show_triangle_components`` (default ``False``) -- if ``True``,
          then the edges in the same $\\triangle$-component have the same color.
        - for other options, see `sage.graphs.generic_graph.GenericGraph.plot() <http://doc.sagemath.org/html/en/reference/graphs/sage/graphs/generic_graph.html#sage.graphs.generic_graph.GenericGraph.plot>`_.
          For instance, ``pos`` specifies the positions of the vertices.

        EXAMPLES::

            sage: from flexrilog import GraphGenerator
            sage: G = GraphGenerator.ThreePrismGraph()
            sage: print(G.plot(NAC_coloring=G.NAC_colorings()[0]))
            Graphics object consisting of 16 graphics primitives

        .. PLOT::
            :width: 70%

            from flexrilog import GraphGenerator
            G = GraphGenerator.ThreePrismGraph()
            sphinx_plot(G.plot(NAC_coloring=G.NAC_colorings()[0]))

        ::

            sage: G.triangle_connected_components()
            [[[0, 3], [0, 4], [3, 4]], [[1, 2], [1, 5], [2, 5]], [[0, 5]], [[1, 4]], [[2, 3]]]
            sage: print(G.plot(show_triangle_components=True))
            Graphics object consisting of 16 graphics primitives

        .. PLOT::
            :width: 70%

            from flexrilog import GraphGenerator
            G = GraphGenerator.ThreePrismGraph()
            sphinx_plot(G.plot(show_triangle_components=True))

        ::

            sage: print(G.plot(pos={0: [0.3, 0.5], 1: [0, 2], 2: [1, 1.4], 3: [1, 0], 4: [0, 0], 5: [0.7, 1]}))
            Graphics object consisting of 16 graphics primitives

        .. PLOT::
            :width: 70%

            from flexrilog import GraphGenerator
            G = GraphGenerator.ThreePrismGraph()
            sphinx_plot(G.plot(pos={0: [0.3, 0.5], 1: [0, 2], 2: [1, 1.4], 3: [1, 0], 4: [0, 0], 5: [0.7, 1]}))
        """
        if show_triangle_components and NAC_coloring:
            raise ValueError('NAC-coloring and triangle components cannot be displayed at the same time.')
        if show_triangle_components:
            triangle_comps = self.triangle_connected_components()
            colors = rainbow(len(triangle_comps))
            kwargs['edge_colors'] = { colors[i] : c for i,c in enumerate(triangle_comps)}
        from .__init__ import colB, colR, colGray
        if isinstance(NAC_coloring, NACcoloring) or 'NACcoloring' in str(type(NAC_coloring)):
            kwargs['edge_colors'] = {
                colB : NAC_coloring.blue_edges(),
                colR : NAC_coloring.red_edges()
                }
        if self.name() and name_in_title:
            kwargs['title'] = self.name()
        if not 'vertex_color' in kwargs:
            kwargs['vertex_color'] = colGray
        if not 'edge_thickness' in kwargs: 
            kwargs['edge_thickness'] = 4
        return Graph(self).plot(**kwargs)

    @doc_index("Plotting")
    def show_all_NAC_colorings(self, ncols=3, only_return=False):
        r"""
        Show all NAC-colorings of the graph.
        
        The parameter ``ncols`` specifies in how many columns are the NAC colorings displayed. 
        """
        from sage.all import graphics_array
        if ncols==1 and not only_return:
            for delta in self.NAC_colorings():
                show(delta.plot())
        else:
            figs = graphics_array([delta.plot() for delta in self.NAC_colorings()], ncols=ncols)
            if only_return:
                return figs
            else:
                show(figs)

    @doc_index("NAC-colorings")
    def are_NAC_colorings_named(self):
        r"""
        Return if all NAC-colorings have a unique name.
        """
        return (len(Set([col.name() for col in self.NAC_colorings()])) == len(self.NAC_colorings())
                and self.NAC_colorings()[0].name()!='') 

    @doc_index("NAC-colorings")
    def NAC_colorings_isomorphism_classes(self):
        r"""
        Return partition of NAC-colorings into isomorphism classes.

        See :meth:`flexrilog.NAC_coloring.NACcoloring.is_isomorphic`
        for the definition of two NAC-colorings being isomorphic.

        EXAMPLE::

            sage: from flexrilog import FlexRiGraph
            sage: G = FlexRiGraph(graphs.CompleteBipartiteGraph(2,3))
            sage: isomorphism_classes = G.NAC_colorings_isomorphism_classes()
            sage: len(isomorphism_classes)
            3
            sage: [len(cls) for cls in isomorphism_classes]
            [1, 3, 3]
            sage: for cls in isomorphism_classes: print(cls[0])
            NAC-coloring with red edges [[0, 2], [0, 3], [0, 4]] and blue edges [[1, 2], [1, 3], [1, 4]]
            NAC-coloring with red edges [[0, 2], [0, 3], [1, 2], [1, 3]] and blue edges [[0, 4], [1, 4]]
            NAC-coloring with red edges [[0, 2], [0, 3], [1, 4]] and blue edges [[0, 4], [1, 2], [1, 3]]
        """
        if self._NAC_isomorphism_classes:
            return self._NAC_isomorphism_classes
        NACs = self.NAC_colorings()
        if NACs:
            isomorphism_classes=[[NACs[0]]]
            autG = self.automorphism_group()
            for NAC_col in NACs[1:]:
                isomorphic_to_prev = False
                for cls in isomorphism_classes:
                    if NAC_col.is_isomorphic(cls[0], check=False, aut_group=autG):
                        cls.append(NAC_col)
                        isomorphic_to_prev = True
                        break
                if not isomorphic_to_prev:
                    isomorphism_classes.append([NAC_col])
            self._NAC_isomorphism_classes = isomorphism_classes
            return isomorphism_classes
        else:
            return []


    @doc_index("NAC-colorings")
    def set_NAC_colorings_names(self, cls_names=[]):
        r"""
        Set names of NAC-colorings according to isomorphism classes.

        The NAC-colorings in the same class have the same name with a different index.

        INPUT:

        - ``cls_names`` (default ``[]``)-- if specified, then these names are taken for
          the isomorphism classes. Otherwise, Greek letters are taken.

        EXAMPLE::

            sage: from flexrilog import FlexRiGraph
            sage: G = FlexRiGraph(graphs.CompleteBipartiteGraph(2,3))
            sage: G.set_NAC_colorings_names()
            sage: G.NAC_colorings()
            [alpha: NAC-coloring with red edges [[0, 2], [0, 3], [0, 4]] and blue edges [[1, 2], [1, 3], [1, 4]],
            beta1: NAC-coloring with red edges [[0, 2], [0, 3], [1, 2], [1, 3]] and blue edges [[0, 4], [1, 4]],
            gamma1: NAC-coloring with red edges [[0, 2], [0, 3], [1, 4]] and blue edges [[0, 4], [1, 2], [1, 3]],
            beta2: NAC-coloring with red edges [[0, 2], [0, 4], [1, 2], [1, 4]] and blue edges [[0, 3], [1, 3]],
            gamma2: NAC-coloring with red edges [[0, 2], [0, 4], [1, 3]] and blue edges [[0, 3], [1, 2], [1, 4]],
            beta3: NAC-coloring with red edges [[0, 2], [1, 2]] and blue edges [[0, 3], [0, 4], [1, 3], [1, 4]],
            gamma3: NAC-coloring with red edges [[0, 2], [1, 3], [1, 4]] and blue edges [[0, 3], [0, 4], [1, 2]]]
        """
        letters = cls_names + ['alpha', 'beta', 'gamma', 'delta', 'epsilon', 'zeta',
                               'eta', 'theta', 'iota', 'kappa', 'lambda', 'mu', 'nu',
                               'xi', 'pi', 'rho', 'sigma', 'tau', 'upsilon', 'phi', 'varphi',
                               'chi', 'psi', 'omega']
        isomorphism_classes = self.NAC_colorings_isomorphism_classes()
        if len(isomorphism_classes)> len(letters):
            raise RuntimeError('There are not enough letters for all isomorphism classes of NAC-colorings')
        for k, cls in enumerate(isomorphism_classes):
            for i, col in enumerate(cls):
                new_name = letters[k]
                if len(cls)>1:
                    new_name += str(i+1)
                col.set_name(new_name)


    @doc_index('Other')
    def has_min_degree_at_least_three(self):
        r"""
        Return if all vertices have degree at least three.
        """
        return min(self.degree()) >= 3


    @doc_index('Subgraphs')
    def triangles(self):
        r"""
        Return all triangles in the graph.

        OUTPUT:

        List of all triangles given by their vertices.

        EXAMPLES:

        Bipartite graphs have no triangles::

            sage: from flexrilog import FlexRiGraph
            sage: G = FlexRiGraph(graphs.CompleteBipartiteGraph(2,3))
            sage: G.triangles()
            []

        The 3-prism graph has two triangles::

            sage: from flexrilog import GraphGenerator
            sage: G = GraphGenerator.ThreePrismGraph()
            sage: G.triangles()
            [[0, 3, 4], [1, 2, 5]]

        The complete graph on 5 vertices::

            sage: len(FlexRiGraph(graphs.CompleteGraph(5)).triangles()) == binomial(5,3)
            True
        """
        res=[]
        for u,v in self.edges(labels=False):
            for w in Set(self.neighbors(u)).intersection(Set(self.neighbors(v))):
                res.append(Set([u,v,w]))
        return [list(triangle) for triangle in Set(res)]

    @doc_index('Subgraphs')
    def four_cycles(self, only_with_NAC=False):
        r"""
        Return all 4-cycles in the graph.
        
        INPUT:

        - ``only_with_NAC`` (default ``False``) -- if ``True``, then a 4-cycle is in the returned list
          only if there exists a NAC-coloring of the graph which is not unicolor on the 4-cycle. 

        OUTPUT:

        List of all (in terms of the vertex set) 4-cycles given by ordered tuples of their vertices.

        EXAMPLES::

            sage: from flexrilog import GraphGenerator
            sage: G = GraphGenerator.ThreePrismGraph()
            sage: G.four_cycles()
            [(0, 3, 2, 5), (0, 4, 1, 5), (1, 2, 3, 4)]

        ::

            sage: from flexrilog import FlexRiGraph
            sage: len(FlexRiGraph(graphs.CompleteGraph(7)).four_cycles()) == binomial(7,4)*3
            True

        ::

            sage: FlexRiGraph(graphs.CycleGraph(7)).four_cycles()
            []
        """
        res = []
        G = deepcopy(Graph(self))
        for v in G.vertices():
            neigh_v = G.neighbors(v)
            for u1,u2 in Subsets(neigh_v,2):
                for u in Set(G.neighbors(u1)).intersection(Set(G.neighbors(u2))):
                    if u!=v:
                        cycle = (v,u1,u,u2)
                        if only_with_NAC:
                            for delta in self.NAC_colorings():
                                if len(Set([delta.color(u,v) for u,v 
                                            in zip(cycle, list(cycle[1:])+[cycle[0]])]))>1:
                                    res.append(cycle)
                                    break
                        else:
                            res.append(cycle)
            G.delete_vertex(v)
        return res


    @doc_index('Subgraphs')
    def induced_K23s(self):
        r"""
        Return all induced $K_{2,3}$ subgraphs.

        OUTPUT:

        List of all induced $K_{2,3}$ subgraphs given by of their vertices.

        EXAMPLES::

            sage: from flexrilog import GraphGenerator
            sage: G = GraphGenerator.Q1Graph()
            sage: G.induced_K23s()
            [[1, 2, 7, 3, 4], [3, 4, 5, 1, 7], [3, 4, 6, 2, 7]]

        ::

            sage: from flexrilog import FlexRiGraph
            sage: FlexRiGraph(graphs.CompleteGraph(7)).induced_K23s()
            []

        ::

            sage: len(FlexRiGraph(graphs.CompleteBipartiteGraph(4,6)).induced_K23s()) == binomial(4,3)*binomial(6,2) + binomial(4,2)*binomial(6,3)
            True
        """
        res = []
        for u,v,w in Subsets(self.vertices(),3):
            if len(Graph(self).subgraph([u,v,w]).edges()) == 0:
                for x,y in Subsets(Set(self.neighbors(u)
                                       ).intersection(Set(self.neighbors(v))
                                                      ).intersection(Set(self.neighbors(w))),2):
                    if not self.has_edge(x,y):
                        res.append([u,v,w,x,y])
        return res

    @doc_index("NAC-colorings")
    def unicolor_path(self, u, v, active_colorings=None):
        r"""
        Return a unicolor path from ``u`` to ``v``.

        A path is unicolor if for all NAC-colorings $\\delta$ of the graph,
        $|\\{\\delta(e):e\\in E_G\\}|=1$.

        INPUT:

        - ``u`` and ``v`` -- start and endpoint.
        - ``active_colorings`` (default ``None``) -- if specified,
          then only the given colorings are considered instead of all.


        OUTPUT:

        A path given by vertices or ``[]`` if there is none.

        EXAMPLES::

            sage: from flexrilog import GraphGenerator
            sage: G = GraphGenerator.SmallestFlexibleLamanGraph()
            sage: G.unicolor_path(2,3)
            [2, 0, 1, 3]

        ::

            sage: G = GraphGenerator.ThreePrismGraph()
            sage: G.unicolor_path(2,3)
            [2, 3]
            sage: G.has_edge(2,3)
            True
            sage: G.unicolor_path(1,3)
            []

        ::

            sage: G = GraphGenerator.MaxEmbeddingsLamanGraph(8)
            sage: G.unicolor_path(2,4)
            []
            sage: G.unicolor_path(2,4, active_colorings=G.NAC_colorings()[-2:])
            [2, 1, 4]
        """
        if self.has_edge(u,v):
            return [u,v]
        if active_colorings == None:
            active_colorings = self.NAC_colorings()

        paths = self.all_paths(u,v)
        for path in paths:
            is_unicolor_for_all = True
            for col in active_colorings:
                if not col.path_is_unicolor(path):
                    is_unicolor_for_all = False
                    break
            if is_unicolor_for_all:
                return path
        return []


    @doc_index("NAC-colorings")
    def unicolor_pairs(self, active_colorings):
        r"""
        Return pairs of non-adjacent vertices linked by a unicolor path.

        INPUT:

        - ``active_colorings`` -- colorings considered for unicolor paths.

        OUTPUT:

        List of pairs of non-adjacent vertices ``u`` and ``v``
        connected by a unicolor path ``path`` in the form ``[[u,v],path]``.
        """
        res = []
        for u,v in Subsets(self.vertices(),2):
            if not self.has_edge(u,v):
                path = self.unicolor_path(u,v, active_colorings)
                if path:
                    res.append([[u,v],path])
        return res


    @doc_index("NAC-colorings")
    def constant_distance_closure(self, active_colorings=None, save_colorings=False):
        r"""
        Return the constant distance closure of the graph.

        Let $\\operatorname{U}(G)$ denote the set of all pairs $\\{u,v\\}\\subset V_G$ such that $uv\\notin E_G$ and
        there exists a path from $u$ to $v$ which is unicolor for all NAC-colorings $\\delta$ of $G$.
        If there exists a sequence of graphs $G=G_0, \\dots, G_n$ such that
        $G_i=(V_{G_{i-1}},E_{G_{i-1}} \\cup \\operatorname{U}(G_{i-1}))$ for $i\\in\\{1,\\dots,n\\}$
        and $\\operatorname{U}(G_n)=\\emptyset$,
        then the graph $G_n$ is called *the constant distance closure* of $G$.

        INPUT:

        - ``active_colorings`` (default ``None``) -- if specified,
          then they are used instead of all NAC-colorings of the graph.
        - ``save_colorings`` (default ``False``) -- if ``True``,
          then the constant distance closure is returned with the NAC-colorings
          obtained during the computation.

        EXAMPLES::

            sage: from flexrilog import GraphGenerator
            sage: G = GraphGenerator.ThreePrismGraph()
            sage: CDC = G.constant_distance_closure()
            sage: CDC.is_isomorphic(G)
            True

        ::

            sage: G = GraphGenerator.SmallestFlexibleLamanGraph()
            sage: CDC = G.constant_distance_closure()
            sage: CDC.is_isomorphic(graphs.CompleteGraph(5))
            True

        ::

            sage: from flexrilog import FlexRiGraph
            sage: G = FlexRiGraph(1256267)
            sage: CDC = G.constant_distance_closure()
            sage: len(CDC.edges())-len(G.edges())
            1

        TODO:

        An interesting example with less NAC-colorings.
        
        Speed up using triangle-components?
        """
        res = deepcopy(self)
        res._name = 'CDC of ' + res.name()
        if active_colorings == None:
            active_colorings = self.NAC_colorings()
        upairs = res.unicolor_pairs(active_colorings)
        while upairs:
            res.add_edges([e for e,_ in upairs])
            active_res = []
            for col in active_colorings:
                red = col.red_edges()
                blue = col.blue_edges()
                for e, path in upairs:
                    if col.is_red(path[0:2]):
                        red.append(e)
                    else:
                        blue.append(e)
                if col._name:
                    col_new = NACcoloring(res, [red, blue], check=False, name=col._name)
                else:
                    col_new = NACcoloring(res, [red, blue], check=False)
                if col_new.is_NAC_coloring():
                    active_res.append(col_new)
            active_colorings = active_res
            upairs = res.unicolor_pairs(active_colorings)
        if save_colorings:
            res._NAC_colorings = active_colorings
            res._NACs_computed = True
        return res

    @doc_index("NAC-colorings")
    def cdc_is_complete(self, active_colorings=None):
        r"""
        Return if the constant distance closure is the complete graph.

        **Theorem** [GLS2018a]_

        A graph $G$ is movable if and only the constant distance closure of $G$ is movable.

        **Corollary**

        If $G$ is movable, then the constant distance closure of $G$ is not complete.

        EXAMPLES::

            sage: from flexrilog import GraphGenerator
            sage: G = GraphGenerator.ThreePrismGraph()
            sage: G.cdc_is_complete()
            False

        ::

            sage: G = GraphGenerator.SmallestFlexibleLamanGraph()
            sage: G.cdc_is_complete()
            True

        ::

            sage: G = GraphGenerator.MaxEmbeddingsLamanGraph(7)
            sage: G.cdc_is_complete()
            True
        """
        return self.constant_distance_closure(active_colorings).is_complete()


    @doc_index("Movability")
    def has_injective_grid_construction(self, certificate=False):
        r"""
        Return if there is a NAC-coloring with injective grid coordinates.

        See :meth:`flexrilog.NAC_coloring.NACcoloring.grid_coordinates`.

        INPUT:

        - ``certificate`` (boolean) -- if ``False`` (default),
          then only boolean value is returned.
          Otherwise, the output is ``(True, delta)`` or ``(False, None)``,
          where the ``delta`` is a NAC-coloring giving injective grid construction.

        EXAMPLES::

            sage: from flexrilog import GraphGenerator
            sage: G = GraphGenerator.ThreePrismGraph()
            sage: G.has_injective_grid_construction(certificate=True)
            (True, NAC-coloring with red edges [[0, 3], [0, 4], [1, 2], [1, 5], [2, 5], [3, 4]] and blue edges [[0, 5], [1, 4], [2, 3]])

        ::

            sage: from flexrilog import GraphGenerator
            sage: G = GraphGenerator.SmallestFlexibleLamanGraph()
            sage: G.has_injective_grid_construction()
            False
        """
        for col in self.NAC_colorings():
            if col.grid_coordinates_are_injective():
                if certificate:
                    return (True, col)
                else:
                    return True
        if certificate:
            return (False, None)
        else:
            return False


    @doc_index("Movability")
    def spatial_embeddings_four_directions(self, delta_1, delta_2, vertex_at_origin=None):
        r"""
        Return injective embeddings in $\\mathbb{R}^3$ with edges in 4 directions.

        The method attempts to embedd injectively the vertices of the graph into $\\mathbb{R}^3$
        so that two edges are parallel if and only if
        they obtain the same colors by ``delta_1`` and ``delta_2``.
        The four possible directions are (1,0,0), (0,1,0), (0,0,1) and (-1,-1,-1).
        If such an embedding exists, then the graph is movable:

        **Lemma** [GLS2018a]_

        Let $G=(V,E)$ be a graph with an injective embedding $\\omega:V\\rightarrow\\mathbb{R}^3$
        such that for every edge $uv\in E$, the vector $\\omega(u)-\\omega(v)$ is parallel
        to one of the four vectors $(1,0,0)$, $(0,1,0)$, $(0,0,1)$, $(-1,-1,-1)$,
        and all four directions are present. Then $G$ is movable.

        Moreover, there exist two NAC-colorings such that two edges are parallel in the embedding $\\omega$ if and only if they
        receive the same pair of colors.

        INPUT:

        - ``delta_1`` and ``delta_2`` -- NAC-colorings
        - ``vertex_at_origin`` -- if ``None`` (default),
          then the first vertex is placed to the origin.

        OUTPUT:

        A dictionary with parametrized positions of vertices,
        if the embedding exists, otherwise ``None``.

        EXAMPLE::

            sage: from flexrilog import GraphGenerator
            sage: G = GraphGenerator.Q1Graph()
            sage: G.spatial_embeddings_four_directions(G.name2NAC_coloring('epsilon13'), G.name2NAC_coloring('epsilon24'))
            {1: (0, 0, 0),
             2: (2*a, a, a),
             3: (a, a, a),
             4: (a, 0, 0),
             5: (0, -a, 0),
             6: (2*a, a, 2*a),
             7: (a, 0, a)}
        """
        if vertex_at_origin == None:
            vertex_at_origin = self.vertices()[0]

        x = {}
        y = {}
        z = {}
        for u in self.vertices():
            x[u] = var('x'+str(u))
            y[u] = var('y'+str(u))
            z[u] = var('z'+str(u))

        equations = []
        for u,v in self.edges(labels=False):
            if delta_1.is_red(u, v) and delta_2.is_blue(u, v): #rb (0,0,1)
                equations.append(x[u]-x[v])
                equations.append(y[u]-y[v])
            if delta_1.is_red(u, v) and delta_2.is_red(u, v): #rr (-1,-1,-1)
                equations.append(x[u]-x[v]-(y[u]-y[v]))
                equations.append(x[u]-x[v]-(z[u]-z[v]))
            if delta_1.is_blue(u, v) and delta_2.is_blue(u, v): #bb (1,0,0)
                equations.append(y[u]-y[v])
                equations.append(z[u]-z[v])
            if delta_1.is_blue(u, v) and delta_2.is_red(u, v): #br (0,1,0)
                equations.append(x[u]-x[v])
                equations.append(z[u]-z[v])

        if not self.has_vertex(vertex_at_origin):
            raise ValueError('The vertex ' + str(vertex_at_origin) + ' is not a vertex of the graph.')

        equations += [x[vertex_at_origin],y[vertex_at_origin],z[vertex_at_origin]]

        for solution in solve(equations, list(chain(x.values(), y.values(), z.values())), solution_dict=True):
            is_injective = True
            for u,v in Subsets(self.vertices(),2):
                if ((solution[x[u]]-solution[x[v]]).is_zero() and
                    (solution[y[u]]-solution[y[v]]).is_zero() and
                    (solution[z[u]]-solution[z[v]]).is_zero()):
                    is_injective = False
                    break
            if is_injective:
                pars = []
                for v in solution.values():
                    pars += (v.variables())
                sub_dict = {}
                i = 0
                for par in Set(pars):
                    if (i==0):
                        sub_dict[par] = var('a')
                    elif (i==1):
                        sub_dict[par] = var('b')
                    else:
                        sub_dict[par] = var('c'+str(i-2))
                    i += 1
                embedding = {}
                for v in self.vertices():
                    embedding[v] = (solution[x[v]].subs(sub_dict),
                                solution[y[v]].subs(sub_dict),
                                solution[z[v]].subs(sub_dict))
                return embedding
        return None


    @doc_index("Movability")
    def has_injective_spatial_embedding(self, certificate=False, onlyOne=True):
        r"""
        Return if there is a spatial embeddings for some pair of NAC-colorings.

        The method runs :meth:`spatial_embeddings_four_directions`
        for all pairs of NAC-colorings of the graph.

        INPUT:

        - ``certificate`` -- if ``False`` (default), then only boolean is returned.
          Otherwise, the output contains also the pair of NAC-colorings giving
          an injective spatial embedding (if it exists, otherwise ``None``).
        - ``onlyOne`` -- if ``True``, then only one pair on NAC-colorings
          is returned as a certificate, otherwise a list of all posibble ones.

        EXAMPLES::

            sage: from flexrilog import GraphGenerator
            sage: G = GraphGenerator.ThreePrismGraph()
            sage: G.has_injective_spatial_embedding(certificate=True)
            (False, None)

        ::

            sage: G = GraphGenerator.Q1Graph()
            sage: G.has_injective_spatial_embedding(certificate=True)
            (True, [eta: NAC-coloring with 7 red edges and 4 blue edges , epsilon24: NAC-coloring with 7 red edges and 4 blue edges ])

        ::

            sage: G.has_injective_spatial_embedding(certificate=True, onlyOne=False) # long time
            (True,
            [[eta: NAC-coloring with 7 red edges and 4 blue edges ,
            ...
            epsilon14: NAC-coloring with 7 red edges and 4 blue edges ]])
        """
        certs = []
        n = len(self.NAC_colorings())
        for i in range(0,n):
            for j in range(i+1,n):
                embd = self.spatial_embeddings_four_directions(self.NAC_colorings()[i],self.NAC_colorings()[j])
                if embd:
                    if certificate:
                        if onlyOne:
                            return (True, [self.NAC_colorings()[i],self.NAC_colorings()[j]])
                        else:
                            certs.append([self.NAC_colorings()[i],self.NAC_colorings()[j]])
                    else:
                        return True
        if certificate:
            if onlyOne:
                return (False, None)
            else:
                return (True, certs)
        else:
            return False


    @doc_index("Movability")
    def is_movable(self):
        r"""
        Return if the graph is movable.

        The method tests the necessary condition :meth:`cdc_is_complete`
        and sufficient ones: :meth:`has_injective_grid_construction`,
        :meth:`has_injective_spatial_embedding` and
        `is_bipartite() <http://doc.sagemath.org/html/en/reference/graphs/sage/graphs/generic_graph.html#sage.graphs.generic_graph.GenericGraph.is_bipartite>`_.

        OUTPUT:

        - If the graph has no NAC-coloring,
          then ``('no', 'no NAC-coloring')`` is returned.
        - If the constant distance closure is the complete graph,
          then ``('no', 'CDC is complete')`` is returned.
        - If the graph is bipartite, then ``('yes', 'bipartite')``
        - If the graph has a NAC-coloring giving an injective grid construction,
          then ``('yes', 'grid construction')``.
        - If the graph has a pair of NAC-coloring giving an injective spatial embedding,
          then ``('yes', 'spatial embedding')``.
        - Otherwise, ``('cannot decide','')``.

        EXAMPLES::

            sage: from flexrilog import GraphGenerator
            sage: GraphGenerator.LamanGraphs(4)[0].is_movable()
            ('no', 'no NAC-coloring')

        ::

            sage: from flexrilog import GraphGenerator
            sage: GraphGenerator.MaxEmbeddingsLamanGraph(7).is_movable()
            ('no', 'CDC is complete')

        ::

            sage: from flexrilog import FlexRiGraph
            sage: FlexRiGraph(graphs.CompleteBipartiteGraph(3,3)).is_movable()
            ('yes', 'bipartite')

        ::

            sage: GraphGenerator.ThreePrismGraph().is_movable()
            ('yes', 'grid construction')

        ::

            sage: GraphGenerator.Q1Graph().is_movable() # long time
            ('yes', 'spatial embedding')

        ::

            sage: GraphGenerator.S1Graph().is_movable() # long time
            ('cannot decide', '')

        ::

            sage: len([G for G in GraphGenerator.LamanGraphs(6) if G.is_movable()[0]=='yes'])
            2

        TODO:

        Graphs with a generic flexible labeling (not spanned by a Laman graph).
        """
        if not self.has_NAC_coloring():
            return ('no', 'no NAC-coloring')
        if self.cdc_is_complete():
            return ('no', 'CDC is complete')
        if self.is_bipartite():
            return ('yes', 'bipartite')
        if self.has_injective_grid_construction():
            return ('yes', 'grid construction')
        if self.has_injective_spatial_embedding():
            return ('yes', 'spatial embedding')
        return ('cannot decide','')



    @doc_index("Rigidity")
    def system_of_equations(self, edge_lengths, fixed_edge):
        r"""
        Return the system of equation for ``edge_lengths``.

        The method returns the system of equations for edge lengths
        with new variables for the squares of distances of vertices
        from the origin in order to decrease the mixed volume of the system.

        INPUT:

        - ``edge_lengths`` -- a dictionary assigning every edge a length.
        - ``fixed_edge`` -- the first vertex is placed to the origin whereas
          the second one on the x-axis.

        OUTPUT:

        A pair ``[eqs, v]`` is returned, where ``eqs` are the equations
        and ``v`` is a vertex adjacent to both vertices of ``fixed_edge``
        if it exists, or ``None`` otherwise. If it exists, then the triangle
        is fixed instead of just the edge, in order to simplify the system.

        EXAMPLES::

            sage: from flexrilog import GraphGenerator
            sage: G = GraphGenerator.ThreePrismGraph()
            sage: L = {(0, 3): 2, (0, 4): 3, (0, 5): 5, (1, 2): 3, (1, 4): 5, (1, 5): 4, (2, 3): 5, (2, 5): 2, (3, 4): 4 }
            sage: G.system_of_equations(L, [4,3])  # random
            [[s5 - 5.25000000000000*x5 - 2.90473750965556*y5 - 16.0000000000000,
            ...
            -x2^2 - y2^2 + s2, -x5^2 - y5^2 + s5], 0]
        """
        def edge_length(u,v):
            if (u,v) in edge_lengths:
                return RR(edge_lengths[(u,v)])
            else:
                return RR(edge_lengths[(v,u)])
        u,v = fixed_edge
        x = {}
        y = {}
        s = {}
        for w in self.vertices():
            s[w] = var('s'+str(w))
            x[w] = var('x'+str(w))
            y[w] = var('y'+str(w))

        x[u] = Integer(0)
        y[u] = Integer(0)
        x[v] = edge_length(u,v)
        y[v] = Integer(0)
        s[u] = Integer(0)
        s[v] = edge_length(u,v)**Integer(2)
        for w in self.neighbors(u):
            s[w] = edge_length(u,w)**Integer(2)
        triangle = Set(self.neighbors(u)).intersection(Set(self.neighbors(v)))
        vertex_in_triangle = None
        for w in triangle:
            x[w] = (x[v]**Integer(2) +edge_length(u,w)**Integer(2) -edge_length(w,v)**Integer(2)
                )/(Integer(2) *x[v])
            y[w] = sqrt(edge_length(u,w)**Integer(2) -x[w]**Integer(2) )
            vertex_in_triangle = w
            break

        eqs_edges = [s[u_]  + s[v_] -Integer(2) *x[u_] * x[v_] -Integer(2) *y[u_] * y[v_] - edge_length(u_,v_)**Integer(2)
                    for u_,v_ in self.edges(labels=False)
                    ]
        eqs_spheres = [s[v_] - (x[v_]**Integer(2)  + y[v_]**Integer(2) ) for v_ in Set(self.vertices())]

        eqs = eqs_edges+eqs_spheres
        return [[eq for eq in eqs if not eq in RR], vertex_in_triangle]


    @doc_index("Rigidity")
    def mixed_volume(self, fixed_edge=None, check=True, full_list=False):
        r"""
        Return the mixed volume of the system of equations if the graph is Laman.

        The method uses `phcpy <http://homepages.math.uic.edu/~jan/phcpy_doc_html/welcome.html>`_
        to compute the mixed volume of the system of equations (``phcpy`` must be installed)
        This gives an upper bound on the number of realizations.

        INPUT:

        - ``fixed_edge`` - the system of equations is constructed
          with this fixed edge. If ``None`` (default),
          then the minimum mixed volume over all edges is returned.
        - ``check`` - if ``True`` (default), then it is checked
          that the graph is Laman.
        - ``full_list`` (default ``False``) - if ``True`` and ``fixed_edge==None``,
          then the list of pairs ``[edge, MV]`` is returned.

        EXAMPLES::

            sage: import phcpy # random, optional - phcpy
            sage: # the previous import is just because of the message that phcpy prints when imported
            sage: from flexrilog import GraphGenerator
            sage: GraphGenerator.ThreePrismGraph().mixed_volume() # optional - phcpy
            32

        ::

            sage: GraphGenerator.MaxEmbeddingsLamanGraph(7).mixed_volume() # optional - phcpy
            64
            sage: GraphGenerator.MaxEmbeddingsLamanGraph(7).mixed_volume([1,5]) # optional - phcpy
            96
            sage: GraphGenerator.MaxEmbeddingsLamanGraph(7).mixed_volume(full_list=True) # optional - phcpy
            [[(1, 2), 128],
            ...
            [(6, 7), 64]]

        """
        from phcpy import solver
        if check and not self.is_Laman():
            raise ValueError('The graph is not Laman')

        L = self.realization2edge_lengths(self.random_realization())

        if fixed_edge:
            eqs, tr_fix = self.system_of_equations(L, fixed_edge)
            eqs_str = [str(eq)+';' for eq in eqs]
            if not solver.is_square(eqs_str):
                raise RuntimeError('The system of equations is not square.')
            multiple = 2 if tr_fix!=None else 1
            return solver.mixed_volume(eqs_str)*multiple
        else:
            MVs = []
            for fixed_edge in self.edges(labels=False):
                eqs, tr_fix = self.system_of_equations(L, fixed_edge)
                eqs_str = [str(eq)+';' for eq in eqs]
                if not solver.is_square(eqs_str):
                    raise RuntimeError('The system of equations is not square.')
                multiple = 2 if tr_fix!=None else 1
                MVs.append([fixed_edge, solver.mixed_volume(eqs_str)*multiple])
            if full_list:
                return MVs
            else:
                return min([mv for _,mv in MVs])


    @doc_index("Rigidity")
    def num_realizations(self, check=True):
        r"""
        Return the number of complex realizations if the graph is Laman.

        The method uses the package `lnumber <https://pypi.org/project/lnumber/>`_ by J. Capco, see also [CGGKLS2018a]_.

        EXAMPLE::

            sage: from flexrilog import GraphGenerator
            sage: [GraphGenerator.MaxEmbeddingsLamanGraph(i).num_realizations() for i in range(6,13)] # optional - lnumber
            [24, 56, 136, 344, 880, 2288, 6180]
        """
        if check and not self.is_Laman():
            raise ValueError('The graph is not Laman')

        from lnumber import lnumber
        return lnumber(self.graph2int(), self.num_verts())


    @doc_index("Rigidity")
    def realizations(self, edge_lengths, fixed_edge=None, check=True,
                     tolerance_real=1e-8,
                     prec='d', num_tasks=2):
        r"""
        Return the realizations for given edge lengths if the graph is Laman.

        The method uses `phcpy <http://homepages.math.uic.edu/~jan/phcpy_doc_html/welcome.html>`_
        to compute the solutions of the system of equations (``phcpy`` must be installed)

        INPUT:

        - ``edge_lengths`` -- a dictionary assigning a length to each edge.
        - ``fixed_edge`` (default ``None``) -- if specified, then it is used
          as the fixed edge. Otherwise, one of the edges giving the minimal mixed
          volume is used
        - ``tolerance_real`` (default 1e-8) -- a solution is considered real if the absolute value
          of the imaginary part of each coordinate is smaller than this number.
        - ``prec`` (default ``'d'``) --  precision used in ``phcpy``:
          ``'d'`` for double precision, ``'dd'`` for double double preicsion (about 32 decimal places)
          and ``'qd'`` for quad double precision (about 64 decimal places).
        - ``num_tasks`` -- number of threads used.

        OUTPUT:

        A pair ``[result_real, result_complex]`` of two lists is returned.
        The first list contains dictionaries with real realizations,
        whereas the second one with the complex solutions.
        If the ``fixed_edge`` is in a 3-cycle, then realizations only with one orienation of 
        the triangle are returned.

        EXAMPLE::

            sage: import phcpy # random, optional - phcpy
            sage: # the previous import is just because of the message that phcpy prints when imported
            sage: from flexrilog import GraphGenerator
            sage: L = {(1, 2): 3, (1, 5): 4, (0, 5): 5, (0, 4): 3, (2, 3): 5, (0, 3): 2, (3, 4): 4, (2, 5): 2, (1, 4): 5}
            sage: res_RR, res_CC = GraphGenerator.ThreePrismGraph().realizations(L,[4,3]); (len(res_RR), len(res_CC)) # optional - phcpy
            (10, 2)
            sage: res_RR # random, optional - phcpy
            [{0: (2.62500000000000, 1.45236875482778),
            1: (-0.988599837464227, 4.90129272349303),
            2: (1.99414754086938, 4.58001702095087),
            3: (4, 0),
            4: (0, 0),
            5: (2.6986546781728, 6.45182622423216)},
            ...
            5: (7.47928649393724, 2.65066030314919)}]

        Some of the realizations from the example above:

        .. PLOT::

            from flexrilog import GraphGenerator
            G = GraphGenerator.ThreePrismGraph()
            L = {(1, 2): 3, (1, 5): 4, (0, 5): 5, (0, 4): 3, (2, 3): 5, (0, 3): 2, (3, 4): 4, (2, 5): 2, (1, 4): 5}
            res_RR, res_CC = G.realizations(L,[4,3])
            sphinx_plot_list([G.plot(pos=rho) for rho in res_RR[2:4]],1,2)

        """
        from phcpy import solver
        from phcpy.solutions import strsol2dict, is_real

        def edge_length(u,v):
            if (u,v) in edge_lengths:
                return edge_lengths[(u,v)]
            else:
                return edge_lengths[(v,u)]

        if check and not self.is_Laman():
            raise ValueError('The graph is not Laman')

        if fixed_edge == None:
            MVs = self.mixed_volume(check=False, full_list=True)
            fixed_edge = min(MVs, key = lambda t: t[1])[0]
        u,v = fixed_edge

        eqs, vertex_in_triangle = self.system_of_equations(edge_lengths, fixed_edge)
        eqs_str = [str(eq)+';' for eq in eqs]

        if not solver.is_square(eqs_str):
            raise RuntimeError('The system of equations is not square.')

        sols = solver.solve(eqs_str, verbose=False, tasks=num_tasks, precision=prec)

        result_real = []
        result_complex = []
        for sol in sols:
            sol_dict = strsol2dict(sol)
            sol_is_real = is_real(sol, tolerance_real)
            for k in copy(sol_dict.keys()):
                if k[0]=='x' or k[0]=='y':
                    if sol_is_real:
                        sol_dict[k] = sol_dict[k].real
                else:
                    sol_dict.pop(k)
            sol_dict['x'+str(u)] = 0
            sol_dict['y'+str(u)] = 0
            sol_dict['x'+str(v)] = edge_length(u,v)
            sol_dict['y'+str(v)] = 0
            if vertex_in_triangle != None:
                w = vertex_in_triangle
                x_v = edge_length(u,v)
                if sol_is_real:
                    x_w = RR((x_v**Integer(2) +edge_length(u,w)**Integer(2) -edge_length(w,v)**Integer(2)
                        )/(Integer(2) *x_v))
                    y_w = RR(sqrt(edge_length(u,w)**Integer(2) -x_w**Integer(2) ))
                    sol_dict['x'+str(w)] = x_w
                    sol_dict['y'+str(w)] = y_w
                else:
                    x_w = CC((x_v**Integer(2) +edge_length(u,w)**Integer(2) -edge_length(w,v)**Integer(2)
                        )/(Integer(2) *x_v))
                    y_w = CC(sqrt(edge_length(u,w)**Integer(2) -x_w**Integer(2) ))
                    sol_dict['x'+str(w)] = x_w
                    sol_dict['y'+str(w)] = y_w

            if sol_is_real:
                result_real.append(sol_dict)
            else:
                result_complex.append(sol_dict)
        for sol_dict in result_real + result_complex:
            for w in self.vertices():
                sol_dict[w] = vector([sol_dict['x'+str(w)], sol_dict['y'+str(w)]])
                sol_dict.pop('x'+str(w))
                sol_dict.pop('y'+str(w))

        return [result_real, result_complex]


    @doc_index("Rigidity")
    def random_realization(self):
        r"""
        Return a random realization of the graph.

        EXAMPLE::

            sage: from flexrilog import GraphGenerator
            sage: GraphGenerator.ThreePrismGraph().random_realization() # random
            {0: (1.2663140331566647, 6.798542831673373),
            ...
            5: (1.938458777654558, 4.519218477998938)}

        """
        realization = {}
        for v in self.vertices():
            realization[v] = vector([10*random.random(),10*random.random()])
        return realization


    @doc_index("Rigidity")
    def realization2edge_lengths(self, realization):
        r"""
        Return the edge lengths for ``realization``.

        EXAMPLE::

            sage: from flexrilog import GraphGenerator
            sage: G = GraphGenerator.ThreePrismGraph()
            sage: G.realization2edge_lengths(G.random_realization()) # random
            {(0, 3): 0.5656854249492381,
            ...
            (3, 4): 1}

        """
        res = {}
        for u,v in self.edges(labels=False):
            res[(u,v)] = norm(vector(realization[u]) - vector(realization[v]))
        return res


    def _swap_xy(self):
        for v in self._pos:
            tmp = self._pos[v][0]
            self._pos[v][0] = self._pos[v][1]
            self._pos[v][1] = tmp

    @doc_index("Plotting")
    def print_tikz(self, colored_edges=[], color_names=['edge'], vertex_style='vertex', scale=1):
        r"""
        Print TikZ code of the graph.
        """
        lowPrecField = RealField(20)
        print('\\begin{tikzpicture}[scale=' + str(lowPrecField(scale)) + ']')
        for k in self.vertices():
            print( '\t\\node[' + vertex_style + '] ('+str(k)+') at '+
                    str((lowPrecField(self._pos[k][0]),lowPrecField(self._pos[k][1])))+' {'+str(k)+'};')
        if len(colored_edges) == len(color_names):
            for subset, col_name in zip(colored_edges, color_names):
                print( '\t\\draw[' + col_name + ']' +
                       ' '.join(['('+str(e[0])+')edge('+str(e[1])+')' for e in subset]) + ';')
        else:
            print( '\t\\draw[edge]' +
                       ' '.join(['('+str(e[0])+')edge('+str(e[1])+')' for e in self.edges()]) + ';')
        print( '\\end{tikzpicture}')

 
   
_additional_categories = {
    FlexRiGraph.plot         : "Plotting",
    }

__doc__ = __doc__.replace(
    "{INDEX_OF_METHODS_FLEXRIGRAPH}", (gen_thematic_rest_table_index(FlexRiGraph, _additional_categories)
   )).replace('**Plotting**', """
**Plotting**
 
.. csv-table::
   :class: contentstable
   :widths: 30, 70
   :delim: @
   
   :meth:`~flexrilog.flexible_rigid_graph.FlexRiGraph.plot` @ Return the plot of the graph.""")



















