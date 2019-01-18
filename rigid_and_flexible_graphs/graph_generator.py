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

            from rigid_and_flexible_graphs.graph_generator import GraphGenerator
            G = GraphGenerator.SmallestFlexibleLamanGraph()
            sphinx_plot(G)
        """
        G = RigidFlexibleGraph([[0,1],[1,2],[0,2],[0,3],[1,3],[2,4],[3,4]], name='SmallestFlexibleLamanGraph',
                           pos={0: [0, 0], 1: [2, 0], 2: [1, 1], 
                                3: [1, -1], 4: [3, 0]})
        return G
