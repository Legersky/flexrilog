# -*- coding: utf-8 -*-
r"""
This is implementation of motions of a graph.

Methods
-------


{INDEX_OF_METHODS}

AUTHORS:

-  Jan Legerský (2019-01-24): initial version

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

from sage.all import deepcopy, Set, Graph#, ceil, sqrt, matrix, copy
from sage.all import SageObject,  parent, Subsets #, rainbow, latex, flatten
from sage.all import vector, matrix, sin, cos, pi,  var,  RR,  floor,  tan
from sage.all import FunctionField, QQ,  sqrt,  function
from sage.misc.rest_index_of_methods import gen_rest_table_index
from sage.rings.integer import Integer
_sage_const_3 = Integer(3); _sage_const_2 = Integer(2); _sage_const_1 = Integer(1);
_sage_const_0 = Integer(0); _sage_const_6 = Integer(6); _sage_const_5 = Integer(5);
_sage_const_4 = Integer(4); _sage_const_13 = Integer(13); _sage_const_12 = Integer(12)
from sage.rings.rational import Rational
from rigid_flexible_graph import RigidFlexibleGraph
import exceptions


class GraphMotion(SageObject):
    r"""

    """
    def __init__(self, graph, input_format, active_NACs, data, check):
        r"""


        TODO:

        Doc, examples
        """
        if not (isinstance(graph, RigidFlexibleGraph) or 'RigidFlexibleGraph' in str(type(graph))):
            raise exceptions.TypeError('The graph must be of the type RigidFlexibleGraph.')
        self._graph = graph
        self._parameter = None
        self._is_parametric = None
        self._par_type = 'symbolic'
        self._field = None
        self._same_lengths = None
        self._active_NACs = None
        if input_format == "grid":
            self._grid2motion(active_NACs[0], data,  check)
        elif input_format == "parametrization":
            self._parametrization2motion(active_NACs, data,  check)
        elif input_format == 'spatial_embedding':
            self._spatial_embedding2motion(active_NACs, data, check)
        else:
            raise exceptions.ValueError('The input format ' + str(input_format) + ' is not supported.')

    def _repr_(self):
        if self._is_parametric:
            return 'Parametric motion with ' + self._par_type + ' parametrization: ' + str(self.parametrization())
        else:
            return 'non-parametric motion is not supported so far!!!'

    @staticmethod
    def GridConstruction(graph,  NAC_coloring,  zigzag=False,  check=True):
        return GraphMotion(graph, 'grid',  [NAC_coloring],  zigzag, check)


    @staticmethod
    def ParametrizedMotion(graph, parametrization, par_type,  active_NACs=None, check=True):
        return GraphMotion(graph, 'parametrization', active_NACs,  { 'parametrization' : parametrization,  'par_type' : par_type}, check)


    @staticmethod
    def Deltoid(par_type='rational'):
        r"""

        TODO:

        Active NACs
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
            G = RigidFlexibleGraph([[0, 1], [1, 2], [2, 3], [0, 3]])
            return GraphMotion.ParametrizedMotion(G, C, 'rational', check=False)
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
            G = RigidFlexibleGraph([[0, 1], [1, 2], [2, 3], [0, 3]])
            return GraphMotion.ParametrizedMotion(G, C, 'symbolic', check=False)



    @staticmethod
    def SpatialEmbeddingConstruction(graph,  active_NACs, check=True, deltoid_motion=None, vertex_at_origin=None, subs_dict={}):
        data = {
                'deltoid_motion' : deltoid_motion,
                'vertex_at_origin' : vertex_at_origin,
                'subs_dict' : subs_dict
                }
        return GraphMotion(graph, 'spatial_embedding', active_NACs, data, check)

    def _grid2motion(self, NAC_coloring, zigzag, check):
        self._is_parametric = True
        self._par_type = 'symbolic'
        alpha = var('alpha')
        self._field = parent(alpha)
        self._parameter = alpha
        self._active_NACs = [NAC_coloring]
        grid_coor = NAC_coloring.grid_coordinates()
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
            raise exceptions.ValueError('The NAC-coloring does not yield a proper flexible labeling.')
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
            positions = {}
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
        self._is_parametric = True
        self._parametrization = data['parametrization']
        element = (sum([self._parametrization[v][0]**Integer(2) for v in self._parametrization])
                    + sum([self._parametrization[v][1]**Integer(2) for v in self._parametrization]))
        self._field = parent(element)
        for v in self._parametrization:
            self._parametrization[v] = vector([self._field(x) for x in self._parametrization[v]])
        if data['par_type'] == 'symbolic':
            self._par_type = 'symbolic'
            if len(element.variables()) != 1:
                raise exceptions.ValueError('The parametrization has to have one parameter (' + str(len(element.variables())) + ' found).')
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
        self._is_parametric = True
        self._par_type = deltoid_motion._par_type
        self._parameter = deltoid_motion._parameter
        self._parametrization = {}
        C = deltoid_motion.parametrization()
        uvf = [C[i+1]-C[i] for i in range(0,3)]
        embedding = self._graph.spatial_embeddings_four_directions(active_NACs[0], active_NACs[1], vertex_at_origin=data['vertex_at_origin'])
        if embedding is None:
            raise exceptions.RuntimeError('There is no injective spatial embeddings.')
        vars = []
        for v in embedding:
            vars += list(embedding[v][0].variables())
            vars += list(embedding[v][1].variables())
        subs_dict = {}
        for vrbl in Set(vars):
            if data['subs_dict'].has_key(str(vrbl)):
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
        if self._is_parametric:
            tmp = {}
            for u, v in self._graph.edges(labels=False):
                s = self._parametrization[u] - self._parametrization[v]
                l = s.inner_product(s)
                if self._par_type == 'rational' and not l in self._field.constant_field():
                    raise exceptions.ValueError('The edge ' + str((u, v)) + ' does not have constant length.')
                if self._par_type == 'symbolic':
                    l = l.simplify_full()
                    if not l.simplify_full().is_constant():
                        raise exceptions.ValueError('The edge ' + str((u, v)) + ' does not have constant length.')
                if tmp.has_key(l):
                    tmp[l].append([u, v])
                else:
                    tmp[l] = [[u, v]]
            self._same_lengths = tmp.values()
        else:
            raise exceptions.NotImplementedError('')

    def edge_lengths(self):
        if self._is_parametric:
            res = {}
            for u, v in self._graph.edges(labels=False):
                s = self._parametrization[u] - self._parametrization[v]
                l = s.inner_product(s)
                if self._par_type == 'rational':
                    if not l in self._field.constant_field():
                        raise exceptions.ValueError('The edge ' + str((u, v)) + ' does not have constant length.')
                    l = self._field.constant_field()(l)
                elif self._par_type == 'symbolic':
                    l = l.simplify_full()
                    if not l.simplify_full().is_constant():
                        raise exceptions.ValueError('The edge ' + str((u, v)) + ' does not have constant length.')
                res[(u, v)] = sqrt(l)
            return res
        else:
            raise exceptions.NotImplementedError('')

    def parametrization(self):
        r"""
        Return the parametrization.

        TODO:

        Doc, examples
        """
        if self._is_parametric:
            return deepcopy(self._parametrization)
        else:
            raise exceptions.RuntimeError('The motion is not parametric.')


    def realization(self, value,  numeric=False):
        r"""
        Return the realization for given value of the parameter.

        TODO:

        Doc, examples
        """
        if self._is_parametric:
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
                raise exceptions.NotImplementedError('')
        else:
            raise exceptions.RuntimeError('The motion is not parametric.')


    def sample_parametrization(self, N,  sampling='uniform'):
        r"""
        Return a sampling of the motion.

        TODO:

        Doc, examples
        """
        if self._is_parametric:
            interval = []
            if type(sampling) == list and len(sampling) == 2:
                sampling_type,  interval = sampling
            else:
                sampling_type = sampling
            if len(interval) != 2:
                a = -pi
                b = pi
            else:
                a, b = interval
            if sampling_type == 'uniform':
                return [self.realization(RR(a + (i/Integer(N)) * (b-a)),  numeric=True) for i in range(0, N+1)]
            elif sampling_type == 'tan':
                return [self.realization(tan(RR(a + (i/Integer(N)) * (b-a))/2.0),  numeric=True) for i in range(0, N+1)]
            else:
                raise exceptions.NotImplementedError('Sampling ' + str(sampling) + ' is not supported.')
        else:
            raise exceptions.RuntimeError('The motion is not parametric.')

    def fix_edge(self, fixed_edge, check=True):
        if self._is_parametric:
            u,v = fixed_edge
            if check and not self._graph.has_edge(u, v):
                raise exceptions.ValueError('The parameter ``fixed_edge`` must be an edge of the graph.')
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
        else:
            raise exceptions.RuntimeError('The motion is not parametric.')


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

    def animation_SVG(self, fileName, sampling='uniform', edge_partition=True, first=None, totalTime=12, width=500,
                           repetitions='indefinite', radius=15, return_IPythonSVG=True, fps=25,
                           flipY=True,
                           rel_margin=0.1, colors=[],
                           rnd_str=True):
        r"""
        Save an SVG animation.

        EXAMPLES::

            sage: from rigid_and_flexible_graphs.graph_generator import GraphGenerator
            sage: G = GraphGenerator.ThreePrismGraph()
            sage: delta = G.NAC_colorings()[0]
            sage: M = GraphMotion.GridConstruction(G, delta.conjugated(), zigzag=[[[0,0], [0,1]], [[0,0], [3/4,1/2], [2,0]]])
            sage: M.animation_SVG('animation')
            <IPython.core.display.SVG object>

        TODO:

        Doc, examples
        """
        if self._is_parametric:
            realizations = self.sample_parametrization(totalTime*fps,  sampling)
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
                hash_object = hashlib.md5(str(time.time()).encode()+str(random()))
                rnd_str = '_' + str(hash_object.hexdigest())[:6] + '_'
            elif type(rnd_str) != str:
                rnd_str = ''

            totalTime = str(totalTime)+'s'
            shift_scale = self._shift_scale_fun(realizations,  rel_margin, width)
            with open(fileName+'.svg','w') as f:
                f.write('<svg width="'+str(width)+'" height="'+str(width)
                        +'"  version="1.1" baseProfile="full"\n') #viewBox="0 0 500 350"
                f.write('xmlns="http://www.w3.org/2000/svg"\n')
                f.write('xmlns:xlink="http://www.w3.org/1999/xlink">\n')
                for v in self._graph.vertices():
                    f.write('  <defs>\n')
                    f.write('<marker id="vertex'+rnd_str+str(v)+'" viewBox="0 0 {1} {1}" refX="{0}" refY="{0}"\n'.format(radius, 2*radius))
                    f.write(' markerWidth="{0}" markerHeight="{0}">\n'.format(floor(radius/3)))
                    f.write('  <circle cx="{0}" cy="{0}" r="{0}" fill="grey" />\n'.format(radius))
                    f.write('<text x="{0:0.0f}" y="{1:0.0f}" font-size="{1}" '.format(float(radius), float(1.5*radius))
                            +'text-anchor="middle" fill="white">'+str(v)+'</text>\n')
                    f.write('</marker>\n')
                    f.write('</defs>\n')

                default_colors = ['LimeGreen','Orchid','Orange','Turquoise','SlateGray','LightGray']
                colors = colors + default_colors

                if edge_partition:
                    if type(edge_partition) == list:
                        pass
                    elif self._same_lengths:
                        edge_partition = self._same_lengths
                else:
                    edge_partition = [self._graph.edges(labels=False)]
                    if len(colors) == len(default_colors):
                        colors = ['LightGray']

                i = 0
                for edges_part in edge_partition:
                    for u,v in edges_part:
                        embd = realizations[first]
                        if i < len(colors):
                            color = colors[i]
                        else:
                            color = 'black'
                        f.write('<path fill="transparent" stroke="'+color+'" stroke-width="5px" id="edge'+rnd_str
                                +str(u)+'-'+str(v)+'"'+
                            ' d="M {:0.0f} {:0.0f} L {:0.0f} {:0.0f}" '.format(*(shift_scale(embd[u]) +
                                                                    shift_scale(embd[v])))
                            +'marker-start="url(#vertex'+rnd_str+str(u)+')"   marker-end="url(#vertex'+rnd_str+str(v)+')" />\n')
                    i += 1

                for edges_part in edge_partition:
                    for u,v in edges_part:
                        f.write('<animate ')
                        f.write('href="#edge'+rnd_str+str(u)+'-'+str(v)+'" ')
                        f.write('attributeName="d" ')
                        f.write('dur="'+totalTime+'" ')
                        f.write('repeatCount="'+str(repetitions)+'" ')
                        f.write('calcMode="linear" ')
                        path_str = ''
                        for embd in realizations[first:]+realizations[:first]: #+[realizations[first]]
                            path_str = path_str+ 'M {:0.0f} {:0.0f} L {:0.0f} {:0.0f};'.format(*(shift_scale(embd[u]) +
                                                                    shift_scale(embd[v])))
                        f.write('values="'+path_str+'"/>\n')

                f.write('</svg>\n')
            if return_IPythonSVG:
                from IPython.display import SVG
                return SVG(fileName+'.svg')
        else:
            raise exceptions.RuntimeError('The motion is not parametric.')

    def height_function(self, vertex_edge_collisions, extra_layers=0, edge_edge_collisions=[]):
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
        for j in range(0, extra_layers + 1):
            i = 1
            res = []
            num_layers = collision_graph.chromatic_number() + j
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
        vertex_coloring = min(res, key = lambda t: t[1])[0]
        h = {}
        for layer in  vertex_coloring:
            for e in vertex_coloring[layer]:
                h[e] = layer
        return h


    def generate_POVray(self, filename, height_function, antialias=True, frames=200, width=1024, height=768, labels=False):
        A = {}
        for v in self._graph.vertices():
            A_min_v = min([height_function[e] for e in height_function if v in e])
            A_max_v = max([height_function[e] for e in height_function if v in e])
            A[v] = [A_min_v, A_max_v]
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
            'Output_File_Name="img_' + filename +'/"',
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
            f.writelines('\n'.join(['#version 3.7;',
                '#include "math.inc"',
                ' ',
                'global_settings {  assumed_gamma 1.0 }',
                'camera{ //ultra_wide_angle',
                '        angle 40',
                '        right z*image_width/image_height',
                '        location  <3.0 , 3.0 , 3.0>',
                '        look_at   <0.0 , 0.3 , 0.0> }',
                'light_source{ <1500,2500,2500>',
                '              color rgb<1,1,1> }',
                'sky_sphere{ pigment{color rgb<1,1,1>}}',
                '',
                '#declare White = rgb <1,1,1>;',
                '#declare Black = rgb <0,0,0>;',
                '#declare LightGray = White*0.8;',
                '#declare DarkGray = White*0.2;',
                '#declare T = clock*2*3.1415 ;']))
            f.write('\n//' +str(self.parametrization()))
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











__doc__ = __doc__.replace(
    "{INDEX_OF_METHODS}", (gen_rest_table_index(GraphMotion)))
