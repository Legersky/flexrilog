# -*- coding: utf-8 -*-
r"""
This is implementation of motions of a graph.

AUTHORS:

-  Jan Legerský (2019-01-24): initial version
-  Jan Legerský (2020-03-12): update to SageMath 9.0

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

from sage.all import deepcopy, Set, Graph, find_root, ceil#, sqrt, matrix, copy
from sage.all import SageObject,  parent, Subsets #, rainbow, latex, flatten
from sage.all import vector, matrix, sin, cos, pi,  var,  RR,  floor,  tan, log
from sage.all import FunctionField, QQ,  sqrt,  function, mod
from sage.misc.rest_index_of_methods import gen_rest_table_index
from sage.rings.integer import Integer
_sage_const_3 = Integer(3); _sage_const_2 = Integer(2); _sage_const_1 = Integer(1);
_sage_const_0 = Integer(0); _sage_const_6 = Integer(6); _sage_const_5 = Integer(5);
_sage_const_4 = Integer(4); _sage_const_13 = Integer(13); _sage_const_12 = Integer(12)
#from sage.rings.rational import Rational
from .flexible_rigid_graph import FlexRiGraph, NACcoloring

class GraphMotion(SageObject):
    def __init__(self, graph):
        if not (isinstance(graph, FlexRiGraph) or 'FlexRiGraph' in str(type(graph))):
            raise TypeError('The graph must be of the type FlexRiGraph.')
        self._graph = graph

        self._same_lengths = None
        self._active_NACs = None

    def _repr_(self):
        return 'An abstract motion of the graph ' + str(self._graph)

    @classmethod
    def GridConstruction(cls, graph,  NAC_coloring,  zigzag=False,  check=True, red_components_ordered=[], blue_components_ordered=[]):
        r"""
        Return the motion obtained by grid construction for given NAC-coloring.
        """
        return ParametricGraphMotion(graph, 'grid',  [NAC_coloring],
                                     {
                                         'zigzag':zigzag,
                                         'red':red_components_ordered,
                                         'blue':blue_components_ordered
                                     }, check)

    
    @classmethod
    def CnSymmetricGridConstruction(cls, G, delta, a_base=[], b_base=[]):
        def Cn_symmetric_points(n, points):
            res=[]
            for p in points:
                res += [matrix(
                    [[RR(cos(RR(Integer(2)*pi*i)/n)), RR(sin(RR(Integer(2) *pi*i)/n))],
                     [RR(-sin(RR(Integer(2)*pi*i)/n)), RR(cos(RR(Integer(2) *pi*i)/n))]]
                    ) * vector(p) for i in range(n)]
            return res
    
        n = delta.n
        
        if a_base==[]:
            a_base = [vector([i, 0]) for i in range(1,len(delta._noninvariant_components['red'])/Integer(n)+1)]
        else:
            n_red = len(delta._noninvariant_components['red'])
            if n*len(a_base)<n_red:
                raise ValueError('There must be {} points in `a_base`, since there are {} red noninvariant components.'.format(n_red/Integer(n), n_red))
        a = Cn_symmetric_points(n, a_base)
        a += [vector([Integer(0) ,Integer(0) ]) for _ in range(len(delta._partially_invariant_components['red']))]
        
        if b_base==[]:
            b_base = [vector([i, 0]) for i in range(1,len(delta._noninvariant_components['blue'])/Integer(n)+1)]
        else:
            n_blue = len(delta._noninvariant_components['blue'])
            if n*len(b_base)<n_blue:
                raise ValueError('There must be {} points in `b_base`, since there are {} blue noninvariant components.'.format(n_blue/Integer(n), n_blue))
        b = Cn_symmetric_points(n, b_base)
        b += [vector([Integer(0) ,Integer(0) ]) for _ in range(len(delta._partially_invariant_components['blue']))]
        
        ab = [b, a]
        M = GraphMotion.GridConstruction(G, delta,
             check=False, zigzag=ab,
             red_components_ordered=delta._noninvariant_components['red']+delta._partially_invariant_components['red'],
             blue_components_ordered=delta._noninvariant_components['blue']+delta._partially_invariant_components['blue'])
    
        for comp in delta._partially_invariant_components['red']+delta._partially_invariant_components['blue']:
            if len(comp)>Integer(1) :
                M.fix_edge(Graph(G).subgraph(comp).edges(labels=False)[Integer(0) ])
                break
        return M

    @classmethod
    def ParametricMotion(cls, graph, parametrization, par_type, active_NACs=None, sampling_type=None, interval=None, check=True):
        r"""
        Return parametric motion of a graph with a given parametrization.

        INPUT:
        
        - ``graph`` -- an instance of FlexRiGraph
        - ``parametrization`` -- a dictionary with a key being a vertex of the graph 
          and its value being the position given as a vector.
        - ``par_type`` -- type of the parametrization: ``rational`` or ``symbolic``
        """
        return ParametricGraphMotion(graph, 'parametrization', active_NACs,
                                     { 'parametrization' : parametrization,
                                     'par_type' : par_type,
                                     'sampling_type' : sampling_type,
                                     'interval' : interval}, check)

    @classmethod
    def Deltoid(cls, par_type='rational'):
        r"""
        Return a deltoid motion.
        """
        if par_type == 'rational':
            FF = FunctionField(QQ, 't')
            t = FF.gen()
            C = {
                _sage_const_0 : vector((_sage_const_0 , _sage_const_0 )),
                _sage_const_1 : vector((_sage_const_1 , _sage_const_0 )),
                _sage_const_2 : vector((_sage_const_4 *(t**_sage_const_2  - _sage_const_2
                                                        )/(t**_sage_const_2  + _sage_const_4 ), _sage_const_12 *t/(t**_sage_const_2  + _sage_const_4 ))),
                _sage_const_3 : vector(((t**_sage_const_4  - _sage_const_13 *t**_sage_const_2  + _sage_const_4
                                         )/(t**_sage_const_4  + _sage_const_5 *t**_sage_const_2  + _sage_const_4 ),
                                         _sage_const_6 *(t**_sage_const_3  - _sage_const_2 *t)/(t**_sage_const_4  + _sage_const_5 *t**_sage_const_2  + _sage_const_4 )))
                }
            G = FlexRiGraph([[0, 1], [1, 2], [2, 3], [0, 3]])
            return GraphMotion.ParametricMotion(G, C, 'rational', sampling_type='tan', check=False)
        elif par_type == 'symbolic':
            t = var('t')
            C = {
                _sage_const_0 : vector((_sage_const_0 , _sage_const_0 )),
                _sage_const_1 : vector((_sage_const_1 , _sage_const_0 )),
                _sage_const_2 : vector((_sage_const_4 *(t**_sage_const_2  - _sage_const_2
                                                        )/(t**_sage_const_2  + _sage_const_4 ), _sage_const_12 *t/(t**_sage_const_2  + _sage_const_4 ))),
                _sage_const_3 : vector(((t**_sage_const_4  - _sage_const_13 *t**_sage_const_2  + _sage_const_4
                                         )/(t**_sage_const_4  + _sage_const_5 *t**_sage_const_2  + _sage_const_4 ),
                                         _sage_const_6 *(t**_sage_const_3  - _sage_const_2 *t)/(t**_sage_const_4  + _sage_const_5 *t**_sage_const_2  + _sage_const_4 )))
                }
            G = FlexRiGraph([[0, 1], [1, 2], [2, 3], [0, 3]])
            return ParametricGraphMotion.ParametricMotion(G, C, 'symbolic', sampling_type='tan', check=False)
        else:
            raise ValueError('Deltoid with par_type ' + str(par_type) + ' is not supported.')

    @classmethod
    def SpatialEmbeddingConstruction(cls, graph,  active_NACs,
                                     check=True, four_cycle_motion=None,
                                     vertex_at_origin=None, subs_dict={}):
        r"""
        Return a motion given by spatial embedding construction.

        INPUT:
        
        - ``graph`` -- an instance of FlexRiGraph
        - ``active_NACs`` -- a pair of NAC-colorings used to construct a spatial embedding,
          see :meth:`flexrilog.flexible_rigid_graph.FlexRiGraph.spatial_embeddings_four_directions`.
        - ``four_cycle_motion`` -- a motion of a 4-cycle used to construct the motion of the whole graph.
          If ``None`` (default), then :meth:`Deltoid` is used. 
        """
        data = {
                'deltoid_motion' : four_cycle_motion,
                'vertex_at_origin' : vertex_at_origin,
                'subs_dict' : subs_dict
                }
        return ParametricGraphMotion(graph, 'spatial_embedding', active_NACs, data, check)


    def _minmax_xy(self, embeddings, rel_margin):
        max_x ,max_y, min_x, min_y = (0,0,0,0)
        for embd in embeddings:
            for v in embd:
                max_x = max(max_x, embd[v][0])
                max_y = max(max_y, embd[v][1])
                min_x = min(min_x, embd[v][0])
                min_y = min(min_y, embd[v][1])

        max_x = max_x+rel_margin*(max_x-min_x)
        max_y = max_y+rel_margin*(max_y-min_y)
        min_x = min_x-rel_margin*(max_x-min_x)
        min_y = min_y-rel_margin*(max_y-min_y)
        return min_x,  max_x,  min_y,  max_y

    def _shift_scale_fun(self,  embeddings,  rel_margin, width):
        min_x,  max_x,  min_y,  max_y = self._minmax_xy(embeddings,  rel_margin)
        size_x = max_x-min_x
        size_y = max_y-min_y

        if size_x>size_y:
            def shift_scale(xy):
                x, y = xy
                return [float((x-min_x)*width/size_x), float((y-min_y+(size_x-size_y)/2)*width/size_x)]
        else:
            def shift_scale(xy):
                x, y = xy
                return [float((x-min_x+(-size_x+size_y)/2)*width/size_y), float((y-min_y)*width/size_y)]
        return shift_scale


    def animation_SVG(self, realizations, fileName='', edge_partition=True, first=None, totalTime=12, width=500,
                           repetitions='indefinite', radius='default', return_IPythonSVG=True,
                           flipY=True,
                           rel_margin=0.1, colors=[],
                           rnd_str=True,
                           vertex_labels=True):
        r"""
        Save an SVG animation.

        EXAMPLES::

            sage: from flexrilog import GraphGenerator, GraphMotion
            sage: G = GraphGenerator.ThreePrismGraph()
            sage: delta = G.NAC_colorings()[0]
            sage: M = GraphMotion.GridConstruction(G, delta.conjugated(), zigzag=[[[0,0], [0,1]], [[0,0], [3/4,1/2], [2,0]]])
            sage: M.animation_SVG()
            <IPython.core.display.SVG object>

        TODO:

        Doc, examples
        """
        if first==None:
            first = 2*floor(len(realizations)/3)

        if flipY:
            for embd in realizations:
                for v in embd:
                    embd[v][1] = -embd[v][1]

        if rnd_str == True:
            import hashlib
            import time
            from random import random
            hash_object = hashlib.md5(str(time.time()+random()).encode())
            rnd_str = '_' + str(hash_object.hexdigest())[:6] + '_'
        elif type(rnd_str) != str:
            rnd_str = ''

        totalTime = str(totalTime)+'s'
        shift_scale = self._shift_scale_fun(realizations,  rel_margin, width)

        default_colors = ['LimeGreen','Orchid','Orange','Turquoise','SlateGray','LightGray']
        colors = colors + default_colors
        from .__init__ import colB, colR
        if edge_partition==True and self._same_lengths:
            edge_partition = self._same_lengths
        elif edge_partition=='NAC':
            colors = [colR, colB]
            edge_partition = [
                self._active_NACs[0].red_edges(),
                self._active_NACs[0].blue_edges()
                ]
        elif isinstance(edge_partition, NACcoloring):
            colors = [colR, colB]
            edge_partition = [
                edge_partition.red_edges(),
                edge_partition.blue_edges()
                ]    
        elif type(edge_partition)!=list or len(edge_partition)==0:
                edge_partition = [self._graph.edges(labels=False)]
                if len(colors) == len(default_colors):
                    colors = ['LightGray']
                    
        if radius=='default':
            if vertex_labels:
                radius = 15
            else:
                radius = 8


        lines = []
        lines.append('<svg width="'+str(width)+'" height="'+str(width)
                +'"  version="1.1" baseProfile="full"\n') #viewBox="0 0 500 350"
        lines.append('xmlns="http://www.w3.org/2000/svg"\n')
        lines.append('xmlns:xlink="http://www.w3.org/1999/xlink">\n')
        for v in self._graph.vertices():
            lines.append('  <defs>\n')
            lines.append('<marker id="vertex'+rnd_str+str(v)+'" viewBox="0 0 {1} {1}" refX="{0}" refY="{0}"\n'.format(radius, 2*radius))
            lines.append(' markerWidth="{0}" markerHeight="{0}">\n'.format(floor(radius/3)))
            lines.append('  <circle cx="{0}" cy="{0}" r="{1}" fill="white" stroke="black" stroke-width="2"/>\n'.format(radius, radius-2))
            if vertex_labels:
                lines.append('<text x="{0:0.0f}" y="{1:0.0f}" font-size="{1}" '.format(float(radius), float(1.5*radius))
                        +'text-anchor="middle" fill="black">'+str(v)+'</text>\n')
            lines.append('</marker>\n')
            lines.append('</defs>\n')

        i = 0
        for edges_part in edge_partition:
            for u,v in edges_part:
                embd = realizations[first]
                if i < len(colors):
                    color = colors[i]
                else:
                    color = 'black'
                lines.append('<path fill="transparent" stroke="'+color+'" stroke-width="5px" id="edge'+rnd_str
                        +str(u)+'-'+str(v)+'"'+
                    ' d="M {:0.0f} {:0.0f} L {:0.0f} {:0.0f}" '.format(*(shift_scale(embd[u]) +
                                                            shift_scale(embd[v])))
                    +'marker-start="url(#vertex'+rnd_str+str(u)+')"   marker-end="url(#vertex'+rnd_str+str(v)+')" />\n')
            i += 1

        for edges_part in edge_partition:
            for u,v in edges_part:
                lines.append('<animate ')
                lines.append('href="#edge'+rnd_str+str(u)+'-'+str(v)+'" ')
                lines.append('attributeName="d" ')
                lines.append('dur="'+totalTime+'" ')
                lines.append('repeatCount="'+str(repetitions)+'" ')
                lines.append('calcMode="linear" ')
                path_str = ''
                for embd in realizations[first:]+realizations[:first]: #+[realizations[first]]
                    path_str = path_str+ 'M {:0.0f} {:0.0f} L {:0.0f} {:0.0f};'.format(*(shift_scale(embd[u]) +
                                                            shift_scale(embd[v])))
                lines.append('values="'+path_str+'"/>\n')

        lines.append('</svg>\n')

        if fileName!='':
            with open(fileName+'.svg','w') as f:
                f.writelines(lines)
        if return_IPythonSVG:
            from IPython.display import SVG
            return SVG(''.join(lines))


    def height_function(self, vertex_edge_collisions, extra_layers=0, edge_edge_collisions=[]):
        r"""
        Return a height function of edges if possible for given vertex-edge collisions.

        WARNING:
        
        Costly, since it runs through all edge-colorings.
        """
        def e2s(e):
            return Set(e)
        for v in vertex_edge_collisions:
            vertex_edge_collisions[v] = Set([e2s(e) for e in vertex_edge_collisions[v]])
        collision_graph = Graph([[e2s(e) for e in self._graph.edges(labels=False)],[]],format='vertices_and_edges')
        for u in self._graph.vertices():
            collision_graph.add_edges([[e2s([u,v]),e2s([u,w]),''] for v,w in Subsets(self._graph.neighbors(u),2)])
        for e in collision_graph.vertices():
            for v in vertex_edge_collisions:
                if v in e:
                    for f in vertex_edge_collisions[v]:
                        collision_graph.add_edge([e2s(f), e2s(e), 'col'])
        for e, f in edge_edge_collisions:
            collision_graph.add_edge([e2s(f), e2s(e), 'e-e_col'])
        from sage.graphs.graph_coloring import all_graph_colorings
        optimal = False
        chrom_number = collision_graph.chromatic_number()
        for j in range(0, extra_layers + 1):
            i = 1
            res = []
            num_layers = chrom_number + j
            min_s = len(self._graph.vertices())*num_layers
            for col in all_graph_colorings(collision_graph,num_layers):
                if len(Set(col.keys()))<num_layers:
                    continue
                layers = {}
                for h in col:
                    layers[h] = [u for e in col[h] for u in e]
                col_free = True
                A = []
                for v in vertex_edge_collisions:
                    A_min_v = min([h for h in layers if v in layers[h]])
                    A_max_v = max([h for h in layers if v in layers[h]])
                    A.append([A_min_v, A_max_v])
                    for h in range(A_min_v+1,A_max_v):
                        if v not in layers[h]:
                            if len(Set(col[h]).intersection(vertex_edge_collisions[v]))>0:
                                col_free = False
                                break
                    if not col_free:
                        break
                if col_free:
                    s = 0
                    for v in self._graph.vertices():
                        A_min_v = min([h for h in layers if v in layers[h]])
                        A_max_v = max([h for h in layers if v in layers[h]])
                        s += A_max_v - A_min_v
                    if s<min_s:
                        min_s = s
                        res.append((col, s, A))
                        i += 1
                        if s==2*len(self._graph.edges())-len(self._graph.vertices()):
                            optimal = True
                            break
            if optimal:
                break
        if not res:
            return None
        vertex_coloring = min(res, key = lambda t: t[1])[0]
        h = {}
        for layer in  vertex_coloring:
            for e in vertex_coloring[layer]:
                h[e] = layer
        return h


class ParametricGraphMotion(GraphMotion):
    r"""

    """
    def __init__(self, graph, input_format, active_NACs, data, check):
        r"""


        TODO:

        Doc, examples
        """
        super(ParametricGraphMotion, self).__init__(graph)

        self._parameter = None
        self._par_type = 'symbolic'
        self._field = None

        if (type(data)!=dict or
                not 'sampling_type' in data
                or data['sampling_type']==None):
            self._sampling_type = 'uniform'
        else:
            self._sampling_type = data['sampling_type']
        if (type(data)!=dict or
                not 'interval' in data
                or type(data['interval'])!=list
                or len(data['interval']) < 2):
            if self._sampling_type == 'tan':
                self._interval = [-pi/_sage_const_2, pi/_sage_const_2]
            else:
                self._interval = [-pi, pi]
        else:
            self._interval = [data['interval'][0], data['interval'][1]]
        if input_format == "grid":
            self._grid2motion(active_NACs[0], data,  check)
        elif input_format == "parametrization":
            self._parametrization2motion(active_NACs, data,  check)
        elif input_format == 'spatial_embedding':
            self._spatial_embedding2motion(active_NACs, data, check)
        else:
            raise ValueError('The input format ' + str(input_format) + ' is not supported.')

    def _repr_(self):
        return 'Parametric motion with ' + self._par_type + ' parametrization: ' + str(self.parametrization())

    def _grid2motion(self, NAC_coloring, data, check):
        self._par_type = 'symbolic'
        alpha = var('alpha')
        self._field = parent(alpha)
        self._parameter = alpha
        self._active_NACs = [NAC_coloring]
        zigzag = data['zigzag']
        grid_coor = NAC_coloring.grid_coordinates(ordered_red=data['red'], ordered_blue=data['blue'])
        self._same_lengths = []
        for i, edges in enumerate([NAC_coloring.blue_edges(), NAC_coloring.red_edges()]):
            partition = [[list(edges[0])]]
            for u, v in edges[1:]:
                appended = False
                for part in partition:
                    u2, v2 = part[0]
                    if Set([grid_coor[u][i], grid_coor[v][i]]) == Set([grid_coor[u2][i], grid_coor[v2][i]]):
                        part.append([u, v])
                        appended = True
                        break
                if not appended:
                    partition.append([[u, v]])
            self._same_lengths += partition

        if check and len(Set(grid_coor.values())) != self._graph.num_verts():
            raise ValueError('The NAC-coloring does not yield a proper flexible labeling.')
        if zigzag:
            if type(zigzag) == list and len(zigzag) == 2:
                a = [vector(c) for c in zigzag[0]]
                b = [vector(c) for c in zigzag[1]]
            else:
                m = max([k for _, k in grid_coor.values()])
                n = max([k for k, _ in grid_coor.values()])
                a = [vector([0.3*((-1)**i-1)+0.3*sin(i), i]) for i in range(0,m+1)]
                b = [vector([j, 0.3*((-1)**j-1)+0.3*sin(j)]) for j in range(0,n+1)]
        else:
            m = max([k for _, k in grid_coor.values()])
            n = max([k for k, _ in grid_coor.values()])
            a = [vector([0, i]) for i in range(0,m+1)]
            b = [vector([j, 0]) for j in range(0,n+1)]

        rotation = matrix([[cos(alpha), sin(alpha)], [-sin(alpha), cos(alpha)]])
        positions = {}
        for v in self._graph.vertices():
            positions[v] = rotation * a[grid_coor[v][1]] + b[grid_coor[v][0]]
        self._parametrization = positions

    def _parametrization2motion(self, active_NACs, data,  check):
        self._parametrization = data['parametrization']
        element = (sum([self._parametrization[v][0]**Integer(2) for v in self._parametrization])
                    + sum([self._parametrization[v][1]**Integer(2) for v in self._parametrization]))
        self._field = parent(element)
        for v in self._parametrization:
            self._parametrization[v] = vector([self._field(x) for x in self._parametrization[v]])
        if data['par_type'] == 'symbolic':
            self._par_type = 'symbolic'
            if len(element.variables()) != 1:
                raise ValueError('The parametrization has to have one parameter (' + str(len(element.variables())) + ' found).')
            self._parameter = element.variables()[0]
        if data['par_type'] == 'rational':
            self._par_type = 'rational'
            self._parameter = self._field.gen()
        if check:
            self._edges_with_same_length()

        self._active_NACs = active_NACs

    def _spatial_embedding2motion(self, active_NACs, data,  check):
        r"""
        TODO:

        Same lengths.
        """
        if data['deltoid_motion'] is None:
            deltoid_motion = GraphMotion.Deltoid()
        else:
            deltoid_motion = data['deltoid_motion']
        self._active_NACs = active_NACs
        self._field = deltoid_motion._field
        self._par_type = deltoid_motion._par_type
        self._parameter = deltoid_motion._parameter
        self._interval = deltoid_motion._interval
        self._sampling_type = deltoid_motion._sampling_type
        self._parametrization = {}
        C = deltoid_motion.parametrization()
        uvf = [C[i+1]-C[i] for i in range(0,3)]
        embedding = self._graph.spatial_embeddings_four_directions(active_NACs[0], active_NACs[1], vertex_at_origin=data['vertex_at_origin'])
        if embedding is None:
            raise RuntimeError('There is no injective spatial embeddings.')
        vrs = []
        for v in embedding:
            vrs += list(embedding[v][0].variables())
            vrs += list(embedding[v][1].variables())
        subs_dict = {}
        for vrbl in Set(vrs):
            if str(vrbl) in data['subs_dict']:
                subs_dict[vrbl] = data['subs_dict'][str(vrbl)]
            else:
                subs_dict[vrbl] = Integer(1)
        for v in embedding:
            if self._par_type == 'rational':
                self._parametrization[v] = sum([self._field.constant_field()(xi.subs(subs_dict))*fi for xi,fi in zip(embedding[v],uvf)])
            elif self._par_type == 'symbolic':
                self._parametrization[v] = sum([xi.subs(subs_dict)*fi for xi,fi in zip(embedding[v],uvf)])

        if check:
            self._edges_with_same_length()


    def _edges_with_same_length(self):
        tmp = {}
        for u, v in self._graph.edges(labels=False):
            s = self._parametrization[u] - self._parametrization[v]
            l = s.inner_product(s)
            if self._par_type == 'rational' and not l in self._field.constant_field():
                raise ValueError('The edge ' + str((u, v)) + ' does not have constant length.')
            if self._par_type == 'symbolic':
                l = l.simplify_full()
                if not l.simplify_full().is_constant():
                    raise ValueError('The edge ' + str((u, v)) + ' does not have constant length.')
            if l in tmp:
                tmp[l].append([u, v])
            else:
                tmp[l] = [[u, v]]
        self._same_lengths = tmp.values()

    def edge_lengths(self):
        r"""
        Return the dictionary of edge lengths.
        """
        res = {}
        for u, v in self._graph.edges(labels=False):
            s = self._parametrization[u] - self._parametrization[v]
            l = s.inner_product(s)
            if self._par_type == 'rational':
                if not l in self._field.constant_field():
                    raise ValueError('The edge ' + str((u, v)) + ' does not have constant length.')
                l = self._field.constant_field()(l)
            elif self._par_type == 'symbolic':
                l = l.simplify_full()
                if not l.simplify_full().is_constant():
                    raise ValueError('The edge ' + str((u, v)) + ' does not have constant length.')
            res[(u, v)] = sqrt(l)
        return res

    def parametrization(self):
        r"""
        Return the parametrization.

        TODO:

        Doc, examples
        """
        return deepcopy(self._parametrization)


    def realization(self, value,  numeric=False):
        r"""
        Return the realization for given value of the parameter.

        TODO:

        Doc, examples
        """
        res = {}
        if self._par_type == 'symbolic':
            subs_dict = { self._parameter : value}
            for v in self._graph.vertices():
                if numeric:
                    res[v] = vector([RR(xi.subs(subs_dict)) for xi in self._parametrization[v]])
                else:
                    res[v] = vector([xi.subs(subs_dict) for xi in self._parametrization[v]])
            return res
        elif self._par_type == 'rational':
            h = self._field.hom(value)
            for v in self._graph.vertices():
                if numeric:
                    res[v] = vector([RR(h(xi)) for xi in self._parametrization[v]])
                else:
                    res[v] = vector([h(xi) for xi in self._parametrization[v]])
            return res
        else:
            raise NotImplementedError('')


    def sample_motion(self, N, numeric=True, start_margin=0, end_margin=0):
        r"""
        Return a sampling of the motion.

        TODO:

        Doc, examples
        """
        a, b = self._interval
        if numeric:
            if self._sampling_type == 'uniform':
                return [self.realization(RR(a + (i/Integer(N)) * (b-a)),  numeric=True) 
                        for i in range(start_margin, N+1-end_margin)]
            elif self._sampling_type == 'tan':
                return [self.realization(tan(RR(a + (i/Integer(N)) * (b-a))),  numeric=True) 
                        for i in range(start_margin, N+1-end_margin)]
            else:
                raise NotImplementedError('Sampling ' + str(self._sampling_type) + ' is not supported.')
        else:
            if self._sampling_type == 'uniform':
                return [self.realization(a + (i/Integer(N)) * (b-a)) 
                        for i in range(start_margin, N+1-end_margin)]
            elif self._sampling_type == 'tan':
                return [self.realization(tan(a + (i/Integer(N)) * (b-a))) 
                        for i in range(start_margin, N+1-end_margin)]
            else:
                raise NotImplementedError('Sampling ' + str(self._sampling_type) + ' is not supported.')


    def fix_edge(self, edge, check=True):
        r"""
        Change the fixed edge in the motion.
        """
        u,v = edge
        if check and not self._graph.has_edge(u, v):
            raise ValueError('The parameter ``edge`` must be an edge of the graph.')
        res = {}
        direction = self._parametrization[v] - self._parametrization[u]
        l = sqrt(direction.inner_product(direction))
        if self._par_type == 'symbolic':
            l = l.simplify_full()
        for w in self._parametrization:
            tmp = self._parametrization[w] - self._parametrization[u]
            if self._par_type == 'symbolic':
                res[w] = vector([((tmp[0]*direction[0] + tmp[1]*direction[1])/l).simplify_full(),
                            ((tmp[1]*direction[0] - tmp[0]*direction[1])/l).simplify_full()])
            elif self._par_type == 'rational':
                res[w] = vector([((tmp[0]*direction[0] + tmp[1]*direction[1])/l),
                            ((tmp[1]*direction[0] - tmp[0]*direction[1])/l)])
        self._parametrization = res


    def animation_SVG(self, fileName='', edge_partition=True, first=None, totalTime=12, width=500,
                           repetitions='indefinite', radius='default', return_IPythonSVG=True, fps=25,
                           flipY=True,
                           rel_margin=0.1, colors=[],
                           rnd_str=True,
                           vertex_labels=True):
        r"""
        Save an SVG animation.

        EXAMPLES::

            sage: from flexrilog import GraphGenerator, GraphMotion
            sage: G = GraphGenerator.ThreePrismGraph()
            sage: delta = G.NAC_colorings()[0]
            sage: M = GraphMotion.GridConstruction(G, delta.conjugated(), zigzag=[[[0,0], [0,1]], [[0,0], [3/4,1/2], [2,0]]])
            sage: M.animation_SVG()
            <IPython.core.display.SVG object>

        TODO:

        Doc, examples
        """
        realizations = self.sample_motion(totalTime*fps)
        return super(ParametricGraphMotion, self).animation_SVG(realizations, fileName=fileName, edge_partition=edge_partition,
                            first=first, totalTime=totalTime, width=width,
                           repetitions=repetitions, radius=radius, return_IPythonSVG=return_IPythonSVG,
                           flipY=flipY,
                           rel_margin=rel_margin, colors=colors,
                           rnd_str=rnd_str,
                           vertex_labels=vertex_labels)


    def generate_POVray(self, filename, height_function, antialias=True, frames=200, width=1024, height=768, labels=False,
                        camera_location=[3.0 , 3.0 , 3.0], look_at=[0.0 , 0.3 , 0.0],
                        compile_animation=False):
        r"""
        Generate files for POV-ray animation.

        TODO:

        description, make radius as parameter
        """
        A = {}
        for v in self._graph.vertices():
            values = [height_function[e] for e in height_function if v in e]
            A[v] = [min(values), max(values)]
        def transform_rec(expr):
            op = expr.operator()
            operands = expr.operands()
            if op:
                new_op = []
                for operand in operands:
                    new_op.append(transform_rec(operand))
                if str(op)=='<built-in function pow>':
                    return function('pow')(*new_op)
                else:
                    return op(*new_op)
            else:
                return expr
        def transform(expr):
            if self._par_type == 'symbolic':
                return str(transform_rec(expr).subs([self._parameter==var('T')]))
            elif self._par_type == 'rational':
                h = self._field.hom(var('T'))
                return str(transform_rec(h(expr)))
        radius = Integer(1)/Integer(20)
        r_joint = radius
        layer_height = Integer(25)/Integer(100)
        thickness = Integer(2)/Integer(5)

        with open(filename+'.ini','w') as f:
            f.writelines('\n'.join([
            '; POV-Ray animation ini file',
            'Antialias=' + ('On' if antialias else 'Off'),
            'Antialias_Threshold=0.05',
            'Antialias_Depth=6',
            '',
            'Input_File_Name="' + filename +'.pov"',
            'Output_File_Name="' + filename +'_img/"',
            '',
            'Initial_Frame=1',
            'Final_Frame='+str(frames),
            'Initial_Clock=0.0',
            'Final_Clock=1.0',
            '',
            'Width =' + str(width) + ';',
            'Height =' + str(height) + ';',
            '',
            'Cyclic_Animation=on',
            'Pause_when_Done=off']))

        with open(filename+'.pov','w') as f:
            if self._sampling_type == 'uniform':
                samp = '('
            elif self._sampling_type == 'tan':
                samp = 'tan('
            else:
                raise NotImplementedError('Type '+str(self._sampling_type) + 'not implemented.')
            f.writelines('\n'.join(['#version 3.7;',
                '#include "math.inc"',
                ' ',
                'global_settings {  assumed_gamma 1.0 }',
                'camera{ //ultra_wide_angle',
                '        angle 40',
                '        right z*image_width/image_height',
                '        location  <{}, {}, {}>'.format(*camera_location),
                '        look_at   <{}, {}, {}>'.format(*look_at) +'}',
                'light_source{ <1500,2500,2500>',
                '              color rgb<1,1,1> }',
                'sky_sphere{ pigment{color rgb<1,1,1>}}',
                '',
                '#declare White = rgb <1,1,1>;',
                '#declare Black = rgb <0,0,0>;',
                '#declare LightGray = White*0.8;',
                '#declare DarkGray = White*0.2;',
                ('#declare T = ' + samp
                    + str(RR(self._interval[0]))
                    + ' + clock*' + str(RR(self._interval[1]-self._interval[0]))
                    + ');')
                ]))
            f.write('\n// parametrization: ' +str(self.parametrization()))
            for e in self._graph.edges(labels=False):
                f.write('\n// ' + str(e))
                f.write('\ncylinder{')
                for i in [0,1]:
                    f.write('<' + transform(self.parametrization()[e[i]][0]) + ','
                        + str(layer_height *height_function[Set(e)])  + ',' +transform(self.parametrization()[e[i]][1]) + '>,')
                f.write(str(radius))
                f.write('\ntexture{ pigment { color LightGray}')
                f.write('\nfinish  { phong 1}')
                f.write('\n   }')
                f.write('\n}')

                for v in e:
                    f.write('\ncylinder{')
                    f.write('<' + transform(self.parametrization()[v][0]) + ','
                        + str(layer_height *(height_function[Set(e)]-thickness)) + ',' + transform(self.parametrization()[v][1]) + '>,')
                    f.write('<' + transform(self.parametrization()[v][0]) + ','
                        + str(layer_height *(height_function[Set(e)]+thickness)) + ',' + transform(self.parametrization()[v][1]) + '>,')
                    f.write(str(radius*2))
                    f.write('\ntexture{ pigment { color DarkGray}')
                    f.write('\nfinish  { phong 1}')
                    f.write('\n   }')
                    f.write('\n}')

            for v in self._graph.vertices():
                f.write('cylinder{')
                f.write('<' + transform(self.parametrization()[v][0]) + ','
                    + str(layer_height *(A[v][0]-1/2)) + ',' + transform(self.parametrization()[v][1]) + '>,')
                f.write('<' + transform(self.parametrization()[v][0]) + ','
                    + str(layer_height *(A[v][1]+1/2)) + ',' + transform(self.parametrization()[v][1]) + '>,')
                f.write(str(r_joint))
                f.write('\ntexture{ pigment { color Black}')
                f.write('\nfinish  { phong 1}')
                f.write('\n   }')
                f.write('\n}')

                if labels:
                    f.write('\ntext{')
                    f.write('\nttf "timrom.ttf",')
                    f.write('"'+str(v)+ '" 0.1, 0')
                    f.write('\npigment{color rgb<0.5,0,0>}')
                    f.write('\nscale 0.4')
                    f.write('translate <' + transform(self.parametrization()[v][0]) + ',' + str(layer_height *(A[v][1]+Integer(1)/Integer(2))) +
                        ','+ transform(self.parametrization()[v][1]) + '> }')
        if compile_animation:
            name = filename
            import subprocess
            print(subprocess.call(['mkdir', name + '_img']))
            print(subprocess.call(['povray', name+'.ini']))
            print(subprocess.call(['ffmpeg', '-y', '-framerate', '24', '-i',
                             name+'_img/'+name+'%0' + str(len(str(frames))) +'d.png', '-vb', '2M', name+'.mp4']))
            from IPython.display import HTML
            return HTML('<video width="100%" controls> <source src="'+name+'.mp4" type="video/mp4"></video>')


    def _rich_repr_(self, display_manager, **kwds):
        r"""
        Return the rich representation of the object.
        
        TODO:
        
            Check in future versions of SageMath if SVG output works.  
        """
        # copied from GenericGraph
        prefs = display_manager.preferences
        is_small = (0 < self._graph.num_verts() < 20)
        can_plot = (prefs.supplemental_plot != 'never')
        plot_graph = can_plot and (prefs.supplemental_plot == 'always' or is_small)
        # Under certain circumstances we display the plot as graphics
#         if plot_graph:
#             from sage.repl.rich_output.output_graphics import OutputImageSvg
#             return OutputImageSvg(self.animation_SVG(edge_partition=False).data)
        # create text for non-graphical output
        if can_plot or plot_graph:
            text = '{0} \n(use the .animation_SVG() method to show the animation)'.format(repr(self))
        else:
            text = repr(self)
        # latex() produces huge tikz environment, override
        tp = display_manager.types
        if (prefs.text == 'latex' and tp.OutputLatex in display_manager.supported_output()):
            return tp.OutputLatex(r'\text{{{0}}}'.format(text))
        return tp.OutputPlainText(text)


    def collisions(self):
        r"""
        Return vertex-edge collisions.

        OUTPUT:

        A dictionary where key ``v`` is a vertex and the corresponding value
        is a list of edges ``e`` such that ``v`` collides with ``e`` for some parameter value.

        EXAMPLES::

            sage: from flexrilog import GraphMotion
            sage: GraphMotion.Deltoid().collisions()
            {0: [(1, 2), (2, 3)], 1: [(0, 3), (2, 3)], 3: [(0, 1), (1, 2)]}

        ::

            sage: from flexrilog import FlexRiGraph
            sage: t = var('t')
            sage: edges = [(1, 4), (1, 5), (1, 6), (2, 4), (2, 5), (2, 6), (3, 5), (3, 6), (3, 4)]
            sage: M = GraphMotion.ParametricMotion(FlexRiGraph(edges),
            ....:     {1: vector([sin(t),0]), 2: vector([sqrt(1+sin(t)^2),0]), 3: vector([-sqrt(2+sin(t)^2),0]),
            ....:     4: vector([0,cos(t)]), 5: vector([0,sqrt(1+cos(t)*cos(t))]), 6: vector([0,-sqrt(2+cos(t)^2)])},
            ....:     'symbolic')
            sage: M.collisions()
            {1: [(3, 4), (2, 4)], 4: [(1, 5), (1, 6)]}


        WARNING:

        It is not guaranteed that all collisions are found,
        since it depends on numerical root finding of complicated expressions.
        """
        def find_all_roots(eq, a, b):
            r = find_root(eq, a, b)
            res = [r]
            margin = 0.01
            r_l = r - margin
            r_r = r + margin
            try:
                if a<r_l:
                    res += find_all_roots(eq, a, r_l)
            except RuntimeError:
                pass
            try:
                if r_r<b:
                    res += find_all_roots(eq, r_r, b)
            except RuntimeError:
                pass
            return res
        res = {}
        for u in self._graph:
            res[u] = []
            for v,w in self._graph.edges(labels=False):
                if u in [v, w]:
                    continue
                z = self._parametrization[u] - self._parametrization[v]
                a = z.inner_product(z)
                z = self._parametrization[u] - self._parametrization[w]
                b = z.inner_product(z)
                z = self._parametrization[w] - self._parametrization[v]
                c = z.inner_product(z)
                if self._par_type == 'symbolic':
                    eq = sqrt(a) + sqrt(b) - sqrt(c)
                elif self._par_type == 'rational':
                    h = self._field.hom(var('T'))
                    eq = sqrt(h(a)) + sqrt(h(b)) - sqrt(h(c))
                try:
                    r = find_root(eq, self._interval[0], self._interval[1])
                    res[u].append((v,w))
                except RuntimeError:
                    pass
        for u in self._graph:
            for v,w in self._graph.edges(labels=False):
                if u in [v, w]:
                    continue
                x = self._parametrization[w] - self._parametrization[u]
                y = self._parametrization[v] - self._parametrization[u]
                eq = x[0]*y[1] - y[0]*x[1]
                if self._par_type == 'rational':
                    h = self._field.hom(var('T'))
                    eq = h(eq)
                try:
                    for r in find_all_roots(eq, self._interval[0], self._interval[1]):
                        if self._par_type == 'symbolic':
                            if x[0].subs({self._parameter:RR(r)})!=0:
                                ratio = y[0]/x[0]
                            elif x[1].subs({self._parameter:RR(r)})!=0:
                                ratio = y[1]/x[1]
                            else:
                                res[u].append((v,w))
                                continue
                            if (ratio).subs({self._parameter:RR(r)}) <= 0:
                                res[u].append((v,w))
                        elif self._par_type == 'rational':
                            if h(x[0])!=0:
                                ratio = y[0]/x[0]
                            elif h(x[1])!=0:
                                ratio = y[1]/x[1]
                            else:
                                res[u].append((v,w))
                                continue
                            h = self._field.hom(RR(r))
                            if h(ratio) <= 0:
                                res[u].append((v,w))
                        else:
                            raise NotImplementedError()
                except RuntimeError:
                    pass
        return {v: Set(res[v]).list() for v in res if res[v]}


    def merge_animations(self, motions, total_time=12, fps=25, **kwargs):
        r"""
        Return an animation by concatenating a list of motions.
        """
        realizations = []
        for M in motions:
            realizations += M.sample_motion(floor(total_time*fps/len(motions)))
        return super(ParametricGraphMotion, self).animation_SVG(realizations, **kwargs)


# Methods
# -------
# 
# **GraphMotion**
# 
# {INDEX_OF_METHODS_GRAPH_MOTION}
# 
# **ParametricGraphMotion**
# 
# {INDEX_OF_METHODS_PARAMETRIC_GRAPH_MOTION}

#__doc__ = __doc__.replace(
    #"{INDEX_OF_METHODS_GRAPH_MOTION}", gen_rest_table_index(GraphMotion)).replace(
    #"{INDEX_OF_METHODS_PARAMETRIC_GRAPH_MOTION}", gen_rest_table_index(ParametricGraphMotion))


