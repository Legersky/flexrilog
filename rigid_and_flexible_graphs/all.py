from __future__ import absolute_import

from sage.misc.lazy_import import lazy_import

lazy_import("sage.graphs.graph_generators", "graphs")
lazy_import("sage.graphs.digraph_generators", "digraphs")
lazy_import("sage.graphs.hypergraph_generators", "hypergraphs")

from .rigid_flexible_graph import RigidFlexibleGraph

