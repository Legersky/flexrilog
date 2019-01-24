# -*- coding: utf-8 -*-
r"""
This  module generates some graphs relevant for rigidity and flexibility.


Graphs
-------


{INDEX_OF_METHODS}


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
from sage.misc.rest_index_of_methods import gen_rest_table_index

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
        r"""
        Alias for :meth:`ThreePrismGraph`.
        """
        return GraphGenerator.ThreePrismGraph()

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


    @staticmethod
    def S1Graph():
        r"""
        Return the graph $S_1$.

        EXAMPLE::

            sage: GraphGenerator.S1Graph()
            S_1: RigidFlexibleGraph with 8 vertices and 14 edges

        .. PLOT::
            :scale: 70

            from rigid_and_flexible_graphs.graph_generator import GraphGenerator
            G = GraphGenerator.S1Graph()
            sphinx_plot(G)
        """
        return RigidFlexibleGraph([[6, 1], [2, 3], [5, 4], [4, 3], [6, 3], [6, 5], [1, 2], [8, 3],
                                   [8, 5], [7, 4], [6, 7], [8, 7], [1, 5], [4, 2]],
                                  pos={1: (-1, 0.8), 2: (-2, -0.2), 3: (0, -1), 4: (-1, 0),
                                       5: (0, 1), 6: (1, 0), 7: (0, -1.75), 8: (1.8, 0)},
                                  name='S_1')


    @staticmethod
    def LamanGraphs(n):
        r"""
        Return the Laman graphs with ``n`` vertices.

        See [CGGKLS2018]_.

        INPUT:

        - ``n`` an integer from 3 to 8

        EXAMPLE::

            sage: from rigid_and_flexible_graphs.graph_generator import GraphGenerator
            sage: [len(GraphGenerator.LamanGraphs(n)) for n in range(3,8)]
            [1, 1, 3, 13, 70]
            sage: GraphGenerator.ThreePrismGraph() in GraphGenerator.LamanGraphs(6)
            True
        """
        if n == 3:
            return [RigidFlexibleGraph(Integer(i)) for i in [7]]
        elif n == 4:
            return [RigidFlexibleGraph(Integer(i)) for i in [31]]
        elif n == 5:
            return [RigidFlexibleGraph(Integer(i)) for i in [254, 239, 223]]
        elif n == 6:
            return [RigidFlexibleGraph(Integer(i)) for i in [3326, 4011, 7672, 7916,
                3934, 10479, 6891, 5791, 3447, 12511, 3451, 3311, 3295]]
        elif n == 7:
            return [RigidFlexibleGraph(Integer(i)) for i in [
        120478, 127198, 190686, 104371, 183548, 412894, 102238, 167646, 101630, 
        103932, 103805, 560509, 104055, 112469, 112525, 111070, 127575, 190103, 
        104365, 174558, 189853, 186013, 192733, 174823, 111335, 102253, 127567, 
        167773, 113483, 560927, 312735, 102262, 298486, 481867, 1269995, 1270351, 
        190875, 414941, 1256267, 186617, 298919, 401101, 313719, 567671, 104126, 
        123255, 400857, 312759, 102206, 120414, 202335, 200059, 331599, 330991, 
        222443, 567647, 182879, 169631, 659039, 410847, 167711, 174303, 101751, 
        396511, 298223, 104171, 173279, 101743, 101615, 101599]]
        elif n == 8:
            return [RigidFlexibleGraph(Integer(i)) for i in [
        7510520, 19111408, 6739377, 6740393, 8000953, 6462968, 6475132, 6411644, 
        69373436, 6393718, 18995565, 20125169, 20140275, 19617907, 11357278, 
        6411934, 12324062, 6418654, 6418797, 12127482, 69311341, 10964186, 69325181, 
        20126170, 19111826, 170989214, 170990174, 170957470, 204540766, 104368318, 
        104400062, 20584859, 93882590, 210028766, 20093843, 20126547, 210799326, 
        19127059, 160959710, 6419230, 20126603, 35765022, 19118979, 36778783, 
        7877407, 7038046, 7935582, 7947390, 7750878, 12094716, 11636460, 11636216, 
        12703097, 6396410, 13944030, 26774750, 10610910, 6396654, 37850494, 
        12707181, 14191866, 13733610, 69311198, 21091693, 26316494, 22058477, 
        50437485, 6462174, 10833118, 6886654, 10816766, 25283806, 6410494, 25267454, 
        6411870, 10609886, 6393694, 69310174, 6395757, 10800350, 10587870, 10587390, 
        6393086, 6465020, 19174901, 7459635, 6478445, 35829997, 10672733, 19060973, 
        35838077, 7459258, 20026868, 6470121, 10672377, 69376505, 6482285, 6484205, 
        10676461, 69376749, 69380589, 36739453, 10678493, 69390589, 6470554, 
        7444402, 6927794, 7903674, 7935418, 20093404, 19111764, 50568561, 19111820, 
        7909811, 6470492, 6482718, 7942515, 7688563, 8132019, 7950651, 6484765, 
        13669881, 12899677, 13153629, 13161597, 12760537, 21143017, 25271785, 
        25337305, 6461945, 21157213, 25285981, 6395827, 12887533, 21272045, 
        25464301, 12768861, 21157101, 21149133, 25285869, 25277901, 25351389, 
        25337549, 26252765, 25730285, 50503005, 6460921, 6461165, 35755389, 
        35820797, 10652925, 6672166, 20518261, 51481974, 6470539, 10803611, 6465459, 
        10790807, 6609679, 19056061, 69507983, 19187127, 10821356, 12885740, 
        6704926, 6692588, 10833694, 6706846, 10836574, 10835614, 69381007, 35969311, 
        35860269, 6470513, 6482739, 6958893, 37924653, 35860254, 6958878, 6404012, 
        35765043, 6467444, 6405034, 35764021, 6958766, 8130343, 6484597, 35860142, 
        37924526, 37938743, 13166135, 13154895, 25281790, 12895486, 25478391, 
        12887539, 21145075, 21140985, 25269753, 21158479, 12883449, 18993406, 
        10799358, 25466333, 21551215, 21543247, 19190007, 50444623, 19063031, 
        6465423, 35753341, 11585183, 6465143, 10587767, 6692344, 20581749, 20137333, 
        20583837, 20092821, 20093781, 19570453, 50699494, 12897660, 20533367, 
        6704508, 20042519, 11364431, 11881039, 6403925, 6403981, 6478619, 10672795, 
        69376923, 69388731, 36739515, 12339295, 6482703, 6419031, 12142715, 6419215, 
        11880683, 11352267, 11868875, 69325599, 69389087, 12327131, 69391007, 
        11882715, 35838495, 36739871, 7122342, 7638950, 20042142, 51484077, 
        19504918, 50699606, 6954620, 13147772, 35757884, 6966846, 12896179, 
        35868222, 51681511, 21153715, 51491047, 50436019, 13154539, 12892619, 
        35756475, 6887031, 12904783, 21153211, 12895675, 25478559, 26821727, 
        10610327, 6396787, 12696395, 21158123, 21158235, 21150155, 21092715, 
        6493939, 37852603, 6410683, 37850927, 12887951, 18999639, 18998679, 
        26813647, 12756891, 26559695, 6855287, 19467639, 35982711, 6410871, 
        50433399, 21164239, 6480315, 21162319, 35778719, 27004111, 10799547, 
        6624999, 6402791, 21098831, 25898187, 71605071, 22059855, 19190175, 
        84056783, 10805663, 10610263, 6393709, 6461339, 6473147, 35771517, 35763549, 
        18976599, 35778655, 10602159, 35753759, 10667679, 10798495, 19434911, 
        27976853, 28624277, 28887213, 28625293, 6463416, 7653750, 7653806, 8129910, 
        7645670, 20518302, 20027286, 6478522, 20028246, 20093654, 51484083, 
        19570326, 7652790, 20486558, 19126870, 20125581, 35764910, 19603213, 
        19118917, 50699683, 7137575, 7654183, 60082263, 60082319, 60081303, 
        20533535, 6478460, 119047351, 119048367, 117884055, 117885071, 20518679, 
        20107927, 35859898, 6475580, 6958522, 37924282, 6413114, 35763894, 35779127, 
        38837051, 36772667, 7871291, 8136103, 37938493, 20486935, 20585047, 
        19585559, 13165885, 42067261, 110888095, 177489055, 235291807, 20140687, 
        51678631, 236193183, 19512071, 20130631, 50713767, 35772990, 10817516, 
        50967719, 36771518, 38835902, 12881900, 7870142, 50705799, 36743991, 
        25268204, 19618319, 211042527, 19610183, 35778750, 50711847, 36769598, 
        6462456, 7868222, 6773323, 7547723, 13671147, 13674987, 35854587, 7235663, 
        7752271, 8133199, 8145007, 12141693, 12127853, 11357293, 10970317, 8020063, 
        12324077, 13675343, 11422813, 13689071, 11865577, 11226233, 11218153, 
        25511151, 19077839, 12193017, 25576671, 13460559, 12773723, 71474011, 
        12708203, 71479771, 71477739, 71414251, 22059499, 71866747, 83991019, 
        14435423, 14238843, 12773967, 14225003, 13454443, 13067467, 18999695, 
        22073583, 71872863, 84068703, 20006303, 19485855, 42067103, 14421227, 
        71480015, 13519963, 71478095, 71491935, 69325471, 71414607, 22073695, 
        71872751, 84068591, 51419375, 84449519, 36771487, 38835871, 19470575, 
        21534959, 100767391, 71426415, 22071663, 71870831, 84003183, 36778207, 
        75620575, 6415725, 6419023, 8143983, 10606173, 19453087, 7234639, 6772299, 
        35771935, 36738719, 12895471, 36745439, 12805355, 21187947, 6494955, 
        6887803, 71517563, 38931835, 38933755, 100863355, 37950715, 12782971, 
        38868347, 6508795, 31004235, 55776843, 14197997, 26330711, 6888047, 
        21564783, 21370331, 12985819, 21582943, 12888303, 10823919, 25562587, 
        25496815, 30106699, 155852363, 147594827, 147150411, 14191993, 12963177, 
        21287151, 37971055, 26318547, 25796179, 38937839, 38937951, 25479407, 
        84100335, 12902639, 25288943, 19076823, 38868575, 10692255, 21566703, 
        10660511, 10689119, 25800263, 21160175, 6953567, 6639855, 6893807, 7084271, 
        38872431, 25407171, 51449199, 51451119, 25481439, 26297567, 76096735, 
        19091679, 25340127, 50501855, 6462239, 26741983, 6705375, 25562335, 
        13145339, 12684911, 7902814, 13145695, 12750431, 12687083, 21140955, 
        21138923, 12750075, 21091919, 37850735, 36000863, 11617887, 42067039, 
        10587823, 6393647, 21073135, 13944043, 21141199, 36771423, 12756575, 
        100767327, 21139279, 21153007, 21153119, 50435311, 35760479, 18991455, 
        50433375, 26264799, 75810015, 21087599, 12686971, 50500831, 19437791, 
        10653343, 12684655, 25726175, 10587935, 10816735, 6393207, 25267423, 
        6395259, 35753583, 18975983, 6481131, 19434847, 10798303, 10653279, 
        10783967, 6393199, 6393071, 6393055]]

__doc__ = __doc__.replace(
    "{INDEX_OF_METHODS}", (gen_rest_table_index(GraphGenerator))).replace(
    ":func:`~rigid_and_flexible_graphs.graph_generator.",  ":func:`~rigid_and_flexible_graphs.graph_generator.GraphGenerator.")
