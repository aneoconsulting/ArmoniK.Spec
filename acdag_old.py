# TODO:
# - implement naive approach
# - on iterative:
#    - add support for disconnected graphs
#    - generate labeled graphs
#    - implement memoization


import itertools as it
import time

import matplotlib.pyplot as plt
import networkx as nx
import pytest
import rustworkx as rx

from collections import namedtuple
from copy import deepcopy
from pathlib import Path
from typing import cast

from line_profiler import profile
from networkx.algorithms import bipartite


def powerset(iterable):
    "powerset([1,2,3]) --> () (1,) (2,) (3,) (1,2) (1,3) (2,3) (1,2,3)"
    s = list(iterable)
    return it.chain.from_iterable(it.combinations(s, r) for r in range(len(s) + 1))


def labeled_acgraphs(n: int) -> set[rx.PyDiGraph]:
    def node_edge_lists(n_part0: int, n_part1: int):
        Node = namedtuple("Node", ["label", "partition"])
        part1 = [Node(label=i, partition=0) for i in range(n_part0)]
        part2 = [Node(label=i, partition=1) for i in range(n_part1)]
        for subset in powerset(it.chain(
                it.product(range(n_part0), range(n_part0, n_part0 + n_part1)),
                it.product(range(n_part0, n_part0 + n_part1), range(n_part0)))):
            yield part1 + part2, subset

    graphs = set()
    now = 0
    for k in range(3, n + 1):
        now = time.time()
        for size in range(1, k):
            n_part0 = size
            n_part1 = k - size
            for nodes, edges in node_edge_lists(n_part0, n_part1):
                g = rx.PyDiGraph(check_cycle=True, multigraph=False, edge_count_hint=len(edges))
                g.add_nodes_from(nodes)
                try:
                    g.extend_from_edge_list(edges)
                except rx.DAGWouldCycle:
                    continue

                root_indices = [n for n in g.node_indices() if len(g.successor_indices(n)) == 0]
                leave_indices = [n for n in g.node_indices() if len(g.predecessor_indices(n)) == 0]
                if not (all([g.get_node_data(r).partition == 0 for r in root_indices]) and all([g.get_node_data(l).partition == 0 for l in leave_indices])):
                    continue

                graphs.add(g)
        print(f"{k} nodes, {time.time() - now}s, {len(graphs)} graphs")
        now = time.time()
    return graphs


def unlabeled_acgraphs(n: int) -> list[nx.DiGraph]:
    graphs = []

    G = nx.DiGraph()
    G.add_nodes_from([1, 3], partition=0)
    G.add_node(2, partition=1)
    G.add_edges_from([(1, 2), (2, 3)])
    graphs.append(G)

    candidates = [G]
    for k in range(4, n + 1):
        new_candidates = []
        for candidate in candidates:
            for partition in [0, 1]:
                h = candidate.copy()
                h.add_node(k, partition=partition)
                new_candidates.append(h)

            edges = it.chain(it.product([k], range(1, k)), it.product(range(1, k), [k]))
            for edge, partition in it.product(edges, [0, 1]):
                g = candidate.copy()
                g.add_node(k, partition=partition)
                g.add_edge(*edge)

                # if any([nx.is_isomorphic(g, h) for h in graphs]):
                #     continue

                if g.nodes[edge[0]]["partition"] == g.nodes[edge[1]]["partition"]:
                    continue

                if g.nodes[edge[0]]["partition"] == 1 and len([*g.predecessors(edge[1])]) > 1:
                    continue

                if not nx.is_directed_acyclic_graph(g):
                    continue

                roots = {n for n in g.nodes if len([*g.predecessors(n)]) == 0}
                leaves = {n for n in g.nodes if len([*g.successors(n)]) == 0}
                if all([g.nodes[root]["partition"] == 0 for root in roots]) and all([g.nodes[leaf]["partition"] == 0 for leaf in leaves]):
                    graphs.append(g)
                
                new_candidates.append(g)

        candidates = new_candidates

        # for i, candidate in enumerate(candidates):
        #     save_graph_plot(candidate, Path.cwd() / f"graph_{k}_c{i}.png")

    return graphs


def is_valid(G: nx.Graph | nx.DiGraph, partition: int = 0) -> bool:
    """Checks weither a graph is ArmoniK complient, that is:
        - it is a Directed-Acyclic Graph (DAG);
        - it is bipartite;
        - its roots and leaves belongs to the same partition.
    
    Args:
        G: A directed graph.
    
    Return:
        True if the graph is complient, False otherwise.
    """
    if nx.is_empty(G):
        return False

    if not bipartite.is_bipartite(G):
        return False

    if not nx.is_directed_acyclic_graph(G):
        return False

    G = cast(nx.DiGraph, G)

    for n, attr in G.nodes(data=True):
        if attr["partition"] != partition and len(set(G.predecessors(n))) == 0:
            return False
        if attr["partition"] == partition and len(set(G.predecessors(n))) > 1:
            return False
        if attr["partition"] != partition and len(set(G.successors(n))) == 0:
            return False

    return True


G1 = nx.DiGraph()
G1.add_nodes_from([1, 3], partition=0)
G1.add_node(2, partition=1)
G1.add_edges_from([(1, 2), (2, 3)])

@pytest.mark.parametrize(("graph", "expected_return"), [
    (G1, True)
])
def test_is_valid(graph, expected_return):
    assert is_valid(graph) == expected_return


def save_graph_plot(G: nx.Graph, file: Path) -> None:
    pos = nx.nx_agraph.graphviz_layout(G, prog="dot", args="-Grankdir=TB")
    plt.figure()

    # Draw edges and labels separately
    nx.draw_networkx_edges(G, pos, arrows=True)
    nx.draw_networkx_labels(G, pos, font_size=10)

    # Partition-based styling
    part0_nodes = [n for n, d in G.nodes(data=True) if d.get("partition") == 0]
    part1_nodes = [n for n, d in G.nodes(data=True) if d.get("partition") == 1]

    # Draw nodes of partition 0
    nx.draw_networkx_nodes(
        G, pos,
        nodelist=part0_nodes,
        node_color="red",
        node_shape="s"
    )

    # Draw nodes of partition 1
    nx.draw_networkx_nodes(
        G, pos,
        nodelist=part1_nodes,
        node_color="lightgreen",
        node_shape="o"
    )

    plt.axis("off")
    plt.tight_layout()
    plt.savefig(file)
    plt.close()


# for i, g in enumerate(unlabeled_acgraphs(7)):
#     save_graph_plot(g, Path.cwd() / f"valid_{i}.png")

def to_labeled_acgraphs(task_ids: list["str"], object_ids: list["str"]) -> set[rx.PyDiGraph]:
    graphs = set()

    for part0, part1 in it.product(powerset(object_ids), powerset(task_ids)):
        part0 = [Node(label=i, partition=0) for i in part0]
        part1 = [Node(label=i, partition=1) for i in part1]
        print(f"{part0} - {part1}")
        for edges in powerset(it.chain(
                it.product(range(len(part0)), range(len(part0), len(part0 + part1))),
                it.product(range(len(part0), len(part0 + part1)), range(len(part0))))):
            if not edges or not part0 or not part1:
                continue
            g = rx.PyDiGraph(
                check_cycle=True,
                multigraph=False,
                node_count_hint=len(part0 + part1),
                edge_count_hint=len(edges)
            )
            g.add_nodes_from(part0 + part1)
            try:
                g.extend_from_edge_list(edges)
            except rx.DAGWouldCycle:
                continue

            root_indices = [n for n in g.node_indices() if len(g.successor_indices(n)) == 0]
            leave_indices = [n for n in g.node_indices() if len(g.predecessor_indices(n)) == 0]
            if not (all([g.get_node_data(r).partition == 0 for r in root_indices]) and all([g.get_node_data(l).partition == 0 for l in leave_indices])):
                continue

            graphs.add(g)
        # print(f"{k} nodes, {time.time() - now}s, {len(graphs)} graphs")
        now = time.time()
    return graphs

for i, g in enumerate(to_labeled_acgraphs(["t"], ["o", "p"])):
    def node_attr(node):
        if node.partition == 0:
            return {'label': node.label, 'color': 'white', 'fillcolor': 'red', 'style': 'filled', "shape": "square"}
        else:
            return {'label': node.label, 'color': 'black', 'fillcolor': 'green', 'style': 'filled', "shape": "circle"}

    from rustworkx.visualization import graphviz_draw
    graphviz_draw(
        g,
        node_attr_fn=node_attr,
        filename=(Path.cwd() / f"valid_{i}.png"),
        image_type="png",
        # method=""
    )
