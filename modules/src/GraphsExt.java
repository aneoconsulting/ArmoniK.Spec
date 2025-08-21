import com.google.common.collect.Sets;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.logging.ConsoleHandler;
import java.util.logging.Level;
import java.util.logging.Logger;
import java.util.Set;

import org.jgrapht.graph.DefaultEdge;
import org.jgrapht.graph.DirectedAcyclicGraph;

import tlc2.value.impl.RecordValue;
import tlc2.value.impl.SetEnumValue;
import tlc2.value.impl.TupleValue;
import tlc2.value.impl.Value;
import util.UniqueString;

public final class GraphsExt {

	private static final Logger LOGGER = Logger.getLogger(GraphsExt.class.getName());

	private GraphsExt() {
		// no-instantiation!
	}

	/**
     * Generates all valid ArmoniK-compliant graphs (ACGraphs) for the given sets of task and object IDs.
     * <p>
     * A valid graph must satisfy the following constraints:
     * <ul>
     *   <li>Directed and acyclic..</li>
     *   <li>No isolated vertices.</li>
     *   <li>Tasks cannot be root or leaf nodes (must have both predecessors and successors).</li>
     *   <li>Objects cannot have more than one predecessor.</li>
     * </ul>
     * </p>
     *
     * @param t  A set of task IDs (as a TLA+ SetEnumValue).
     * @param o  A set of object IDs (as a TLA+ SetEnumValue).
     * @return   A TLA+ SetEnumValue containing all valid graphs, each represented as a RecordValue
     *           with fields "node" (set of vertices) and "edge" (set of edges).
     * @throws Exception If either input is not a set or if graph generation fails.
     */
	public static Value ACGraphs(final Value t, final Value o)
			throws Exception {
		// Input validation
		if (!(t instanceof SetEnumValue) && t.toSetEnum() == null) {
			throw new Exception(
					"Task IDs must be a set. Value given is of type: " + t.getClass().getName());
		}
		if (!(o instanceof SetEnumValue) && o.toSetEnum() == null) {
			throw new Exception(
					"Object IDs must be a set. Value given is of type: " + o.getClass().getName());
		}
		final SetEnumValue taskIds = (SetEnumValue) t.toSetEnum();
		final SetEnumValue objectIds = (SetEnumValue) o.toSetEnum();

		final Set<Value> taskIdSet = new HashSet<>(Arrays.asList(taskIds.elems.toArray()));
		final Set<Value> objectIdSet = new HashSet<>(Arrays.asList(objectIds.elems.toArray()));

		List<RecordValue> results = new ArrayList<>();

		LOGGER.log(Level.FINE, "Starting ACGraphs with {0} tasks and {1} objects",
                new Object[]{taskIdSet.size(), objectIdSet.size()});

		// Iterate over subsets lazily
		for (Set<Value> objectIdSubset : Sets.powerSet(objectIdSet)) {
			for (Set<Value> taskIdSubset : Sets.powerSet(taskIdSet)) {
				
				// Skip degenerate cases early
                if (objectIdSubset.isEmpty() || taskIdSubset.isEmpty()) {
					LOGGER.log(Level.FINER, "Skipping empty subset: objects={0}, tasks={1}",
                            new Object[]{objectIdSubset, taskIdSubset});
					continue;
				}

				// Generate all possible candidate edges (obj->task and task->obj)
                Set<List<Value>> candidateEdges = new HashSet<>();
                objectIdSubset.forEach(oVal -> taskIdSubset.forEach(tVal -> {
                    candidateEdges.add(List.of(oVal, tVal));
                    candidateEdges.add(List.of(tVal, oVal));
                }));

				// Iterate over all possible edge sets
				for (Set<List<Value>> edges : Sets.powerSet(candidateEdges)) {
					
					// Build the graph
					DirectedAcyclicGraph<Value, DefaultEdge> g =
						new DirectedAcyclicGraph<>(DefaultEdge.class);

					taskIdSubset.forEach(g::addVertex);
					objectIdSubset.forEach(g::addVertex);
					
					// Add edges; skip if a cycle is detected
					try {
						for (List<Value> edge : edges) {
							g.addEdge(edge.get(0), edge.get(1));
						}
					} catch (IllegalArgumentException e) {
						LOGGER.log(Level.FINEST, "Cycle detected in edge set {0}, skipping", edges);
						continue;
					}

					// Validate graph structure
                    if (!isValidGraph(g, taskIdSubset, objectIdSubset)) {
						LOGGER.log(Level.FINER, "Invalid graph filtered: vertices={0}, edges={1}",
                                new Object[]{g.vertexSet(), g.edgeSet()});
						continue;
					}

					// Add valid graph to results
					results.add(toRecordValue(g));
				}
			}
		}

		LOGGER.log(Level.FINE, "Generated {0} valid graphs", results.size());
		return new SetEnumValue(results.toArray(Value[]::new), false);
	}

	/**
     * Validates a graph according to the following rules:
     * <ul>
     *   <li>No isolated vertices (all vertices must have at least one incoming or outgoing edge).</li>
     *   <li>Task vertices cannot be root nodes (must have at least one predecessor).</li>
     *   <li>Task vertices cannot be leaf nodes (must have at least one successor).</li>
     *   <li>Object vertices cannot have more than one predecessor.</li>
     * </ul>
     *
     * @param g        The graph to validate.
     * @param tasks    The set of task vertices.
     * @param objects  The set of object vertices.
     * @return         true if the graph is valid, false otherwise.
     */
	private static boolean isValidGraph(DirectedAcyclicGraph<Value, DefaultEdge> g,
                                        Set<Value> tasks, Set<Value> objects) {
        for (Value v : g.vertexSet()) {
            int succ = g.outDegreeOf(v);
            int pred = g.inDegreeOf(v);

            if (pred == 0 && succ == 0) return false; // isolated
            if (pred == 0 && tasks.contains(v)) return false; // root must be object
            if (succ == 0 && tasks.contains(v)) return false; // leaf must be object
            if (pred > 1 && objects.contains(v)) return false; // object has >1 predecessor
        }
        return true;
    }

	/**
     * Converts a JGraphT DirectedAcyclicGraph to a TLA+ RecordValue.
     * <p>
     * The RecordValue has two fields:
     * <ul>
     *   <li>"node": a set of all vertices in the graph.</li>
     *   <li>"edge": a set of tuples, each representing a directed edge (source, target).</li>
     * </ul>
     * </p>
     *
     * @param g  The graph to convert.
     * @return   A RecordValue representing the graph.
     */
	private static RecordValue toRecordValue(DirectedAcyclicGraph<Value, DefaultEdge> g) {
        UniqueString nodeKey = UniqueString.of("node");
        UniqueString edgeKey = UniqueString.of("edge");

        Value nodes = new SetEnumValue(g.vertexSet().toArray(Value[]::new), false);
        Value edges = new SetEnumValue(
                g.edgeSet().stream()
                        .map(e -> new TupleValue(g.getEdgeSource(e), g.getEdgeTarget(e)))
                        .toArray(Value[]::new),
                false);

        return new RecordValue(new UniqueString[]{nodeKey, edgeKey}, new Value[]{nodes, edges}, false);
    }
}
