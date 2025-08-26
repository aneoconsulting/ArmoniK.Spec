import itertools as it

import rustworkx as rx

from collections import namedtuple
from pathlib import Path

from rustworkx.visualization import graphviz_draw


Node = namedtuple("Node", ["label", "partition"])


def powerset(iterable):
    "powerset([1,2,3]) --> () (1,) (2,) (3,) (1,2) (1,3) (2,3) (1,2,3)"
    s = list(iterable)
    return it.chain.from_iterable(it.combinations(s, r) for r in range(len(s) + 1))


def labeled_acgraphs(task_ids: list["str"], object_ids: list["str"]) -> set[rx.PyDiGraph]:
    graphs = set()
    for part0, part1 in it.product(powerset(object_ids), powerset(task_ids)):
        part0 = [Node(label=i, partition=0) for i in part0]
        part1 = [Node(label=i, partition=1) for i in part1]
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

            invalid = False
            for n in g.node_indices():
                n_preds = len(g.predecessor_indices(n))
                n_succs = len(g.successor_indices(n))

                # Graph with isolated nodes are invalid
                if n_preds == n_succs == 0:
                    invalid = True
                    break

                # Graph with roots not in partition 0 (objects) are invalid
                if n_preds == 0 and g.get_node_data(n).partition != 0:
                    invalid = True
                    break

                # Graph with leaves not in partition 1 (objects) are invalid
                if n_succs == 0 and g.get_node_data(n).partition != 0:
                    invalid = True
                    break

                # Graphs with partition 0 node with more than one predecessor are invalid
                if n_preds > 1 and g.get_node_data(n).partition == 0:
                    invalid = True
                    break

            if invalid:
                continue

            graphs.add(g)
    return graphs


def print_graph(g: rx.PyDiGraph, filename: str):
    def node_attr(node):
        if node.partition == 0:
            return {'label': node.label, 'color': 'white', 'fillcolor': 'red', 'style': 'filled', "shape": "square"}
        else:
            return {'label': node.label, 'color': 'black', 'fillcolor': 'green', 'style': 'filled', "shape": "circle"}

    graphviz_draw(
        g,
        node_attr_fn=node_attr,
        filename=filename,
        image_type="png"
    )


if __name__ == "__main__":
    from collections import defaultdict
    graphs = defaultdict(lambda: [])
    for g in labeled_acgraphs(["t", "u"], ["o", "p", "q"]):
        graphs[g.num_nodes()].append(g)

    for i in range(min(graphs.keys()), max(graphs.keys()) + 1):
        print(f"{i}: {len(graphs[i])}")

    print(f"Total {sum([len(graphs[i]) for i in graphs.keys()])}")

    # for n, li in graphs.items():
    #     for k, g in enumerate(li):
    #         print_graph(g, str(Path.cwd() / f"valid_{n}_{k}.png"))
