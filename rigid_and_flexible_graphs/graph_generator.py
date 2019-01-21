# -*- coding: utf-8 -*-
r"""
Graph Generator
=========================

This  module generates some graphs relevant for rigidity and flexibility.

AUTHORS:

-  Jan Legerský (2019-01-15): initial version
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

from sage.rings.integer import Integer
from rigid_flexible_graph import RigidFlexibleGraph
import exceptions

class GraphGenerator():
    @staticmethod
    def ThreePrismGraph():
        r"""
        Return 3-prism graph.

        EXAMPLES::

            sage: from rigid_and_flexible_graphs.graph_generator import GraphGenerator
            sage: RigidFlexibleGraph([(0, 3), (0, 4), (0, 5), (1, 2), (1, 4), (1, 5), (2, 3), (2, 5), (3, 4)]) == GraphGenerator.ThreePrismGraph()
            True

        .. PLOT::
            :scale: 70

            from rigid_and_flexible_graphs.graph_generator import GraphGenerator
            G = GraphGenerator.ThreePrismGraph()
            sphinx_plot(G)
        """
        G = RigidFlexibleGraph(Integer(7916), name='3-prism',
                           pos={0: [0.6, 0.4], 1: [0, 1.4], 2: [1, 1.4], 
                                3: [1, 0], 4: [0, 0], 5: [0.6, 1]})
        return G

    @staticmethod
    def L1Graph():
        return ThreePrismGraph()

    @staticmethod
    def SmallestFlexibleLamanGraph():
        r"""
        Return the smallest Laman graph that has a flexible labeling.

        EXAMPLES::

            sage: from rigid_and_flexible_graphs.graph_generator import GraphGenerator
            sage: RigidFlexibleGraph([[0,1],[1,2],[0,2],[0,3],[1,3],[2,4],[3,4]]) == GraphGenerator.SmallestFlexibleLamanGraph()
            True

        .. PLOT::
            :scale: 70

            from rigid_and_flexible_graphs.graph_generator import GraphGenerator
            G = GraphGenerator.SmallestFlexibleLamanGraph()
            sphinx_plot(G)
        """
        G = RigidFlexibleGraph([[0,1],[1,2],[0,2],[0,3],[1,3],[2,4],[3,4]], name='SmallestFlexibleLamanGraph',
                           pos={0: [0, 0], 1: [2, 0], 2: [1, 1], 
                                3: [1, -1], 4: [3, 0]})
        return G

    @staticmethod
    def MaxEmbeddingsLamanGraph(n):
        r"""
        Return the Laman graph with ``n`` vertices with the maximum number of complex embeddings.

        See [GKT2018]_.

        INPUT:

        - ``n`` an integer from 6 to 12

        EXAMPLES::

            sage: from rigid_and_flexible_graphs.graph_generator import GraphGenerator
            sage: GraphGenerator.MaxEmbeddingsLamanGraph(6) == GraphGenerator.ThreePrismGraph()
            True

        The graphs:

        .. PLOT::
            :width: 70%

            from rigid_and_flexible_graphs.graph_generator import GraphGenerator
            G = GraphGenerator.MaxEmbeddingsLamanGraph(6)
            sphinx_plot(G)

        .. PLOT::
            :width: 70%

            from rigid_and_flexible_graphs.graph_generator import GraphGenerator
            G = GraphGenerator.MaxEmbeddingsLamanGraph(7)
            sphinx_plot(G)


        .. PLOT::
            :width: 70%

            from rigid_and_flexible_graphs.graph_generator import GraphGenerator
            G = GraphGenerator.MaxEmbeddingsLamanGraph(8)
            sphinx_plot(G)

        .. PLOT::
            :width: 70%

            from rigid_and_flexible_graphs.graph_generator import GraphGenerator
            G = GraphGenerator.MaxEmbeddingsLamanGraph(9)
            sphinx_plot(G)

        .. PLOT::
            :width: 70%

            from rigid_and_flexible_graphs.graph_generator import GraphGenerator
            G = GraphGenerator.MaxEmbeddingsLamanGraph(10)
            sphinx_plot(G)

        .. PLOT::
            :width: 70%

            from rigid_and_flexible_graphs.graph_generator import GraphGenerator
            G = GraphGenerator.MaxEmbeddingsLamanGraph(11)
            sphinx_plot(G)

        .. PLOT::
            :width: 70%

            from rigid_and_flexible_graphs.graph_generator import GraphGenerator
            G = GraphGenerator.MaxEmbeddingsLamanGraph(12)
            sphinx_plot(G)
        """
        graph_repr = {
            6 : 7916,
            7 : 1269995,
            8 : 170989214,
            9 : 11177989553,
            10 : 4778440734593,
            11 : 18120782205838348,
            12 : 252590061719913632,
            }
        positions = {
            7 : {5: (-1, -1), 2: (1, -1), 1: (2.5, 2), 4: (-1, 1), 3: (1, 1), 0: (-2.5, 2), 6: (0, 0)},
            8 : {6 : (-0.00,-17.00), 7 : (2.5,7.24), 4 : (7.50,0.00), 5 : (-0.00,-7.24), 
                 3 : (20.00,0.00), 1 : (-20.00,0.00), 2 : (-7.50,0.00), 0 : (-0.00,19.00)},
            9: {8 : (21.00,2.00), 7 : (-5.10,20.00) , 6 : (0.17,-5.70) , 3 : (7.90,-2.80) , 2 : (-5.10,-16.00) ,
                5 : (0.17,9.70) , 4 : (-8.20,2.00) , 0 : (7.90,6.80) , 1 : (-19.00,2.00) ,},
            10 : {9 : (-20.00,-16.00), 8 : (20.00,-16.00), 6 : (-0.00,-2.30), 7 : (-0.00,13.00), 4 : (-9.10,-0.20),
                  5 : (9.10,-0.20), 1 : (-6.00,-11.00), 0 : (-12.00,21.00), 2 : (6.00,-11.00), 3 : (12.00,21.00)},
            11: {9 : (7.20,6.80), 8 : (20.00,2.00), 10 : (-7.20,6.80), 7 : (-20.00,2.00), 6 : (0.00,-6.60),
                 2 : (7.20,-2.80), 3 : (0.00,2.00), 4 : (0.00,-16.00), 5 : (-7.20,-2.80), 0 : (0.00,10.60), 1 : (0.00,20.00)},
            12: {11 : (20.00,-12.00), 6 : (-20.00,-12.00), 10 : (7.80,6.20), 7 : (-8.30,-3.90), 9 : (8.30,-3.90), 8 : (-7.80,6.20),
                 0 : (15.00,0.85), 1 : (20.00,14.00), 2 : (0.00,-2.10), 3 : (-20.00,14.00), 4 : (0.00,-7.80), 5 : (-15.00,0.85)}
            }
        if n == 6:
            return GraphGenerator.ThreePrismGraph()
        if n > 6 and n < 13:
            return RigidFlexibleGraph(Integer(graph_repr[n]), pos=positions[n], name='MaxEmbeddingsLamanGraph_' + str(n) + 'vert')
        else:
            raise exceptions.ValueError('Only graphs with 6-12 vertices are supported.')

    @staticmethod
    def Q1Graph():
        r"""
        Return the graph $Q_1$.

        EXAMPLE::

            sage: from rigid_and_flexible_graphs.graph_generator import GraphGenerator
            sage: GraphGenerator.Q1Graph()
            Q_1: RigidFlexibleGraph with 7 vertices and 11 edges

        .. PLOT::
            :scale: 70

            from rigid_and_flexible_graphs.graph_generator import GraphGenerator
            G = GraphGenerator.Q1Graph()
            sphinx_plot(G)
        """
        return RigidFlexibleGraph([(0, 1), (0, 2), (0, 6), (1, 2), (1, 4), (1, 5), (2, 3), (3, 4), (3, 5), (4, 6), (5, 6)],
                                  pos={5 : (0.500, 0.866), 4 : (-0.500, 0.866), 6 : (-1.00, 0.000), 3 : (1.00, 0.000), 
                                       2 : (0.500, -0.866), 0 : (-0.500, -0.866), 1 : (0.000, 0.000)},
                                  name='Q_1')
