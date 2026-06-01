import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.logging.Level;
import java.util.logging.Logger;

import tlc2.value.impl.RecordValue;
import tlc2.value.impl.SetEnumValue;
import tlc2.value.impl.TupleValue;
import tlc2.value.impl.Value;
import util.UniqueString;

public final class DDGraphs {

    private static final Logger LOGGER = Logger.getLogger(DDGraphs.class.getName());

    private static final UniqueString NODE_KEY = UniqueString.of("node");
    private static final UniqueString EDGE_KEY = UniqueString.of("edge");
    // TLC's UniqueString.compareTo orders by interning tag (allocation order),
    // not lexically. We pre-sort by that comparator so the resulting record
    // is "already normalized" and matches the canonical layout TLC's parser
    // produces for [node |-> ..., edge |-> ...] literals.
    private static final UniqueString[] RECORD_NAMES;
    private static final boolean NODE_FIRST;
    static {
        if (NODE_KEY.compareTo(EDGE_KEY) <= 0) {
            RECORD_NAMES = new UniqueString[]{NODE_KEY, EDGE_KEY};
            NODE_FIRST = true;
        } else {
            RECORD_NAMES = new UniqueString[]{EDGE_KEY, NODE_KEY};
            NODE_FIRST = false;
        }
    }

    private static RecordValue makeRecord(Value nodeSet, Value edgeSet) {
        Value[] values = NODE_FIRST
                ? new Value[]{nodeSet, edgeSet}
                : new Value[]{edgeSet, nodeSet};
        return new RecordValue(RECORD_NAMES, values, true);
    }

    private DDGraphs() {
        // no-instantiation
    }

    /**
     * Java overload of the TLA+ operator {@code DDGraphOf(T, O)} defined in
     * {@code DDGraphs.tla}. Returns the set of all Data-Dependency graphs over
     * task ids {@code T} and object ids {@code O}.
     * <p>
     * A graph {@code g = [node, edge]} belongs to the result iff there exists a
     * pair {@code (t, o)} with {@code t} a subset of {@code T} and {@code o} a
     * subset of {@code O} such that:
     * <ul>
     *   <li>{@code g.node} equals {@code t} union {@code o};</li>
     *   <li>{@code g.edge} is a subset of {@code (t x o) cup (o x t)};</li>
     *   <li>{@code g} is a DAG;</li>
     *   <li>every root of {@code g} is in {@code o} (tasks are never roots);</li>
     *   <li>every leaf of {@code g} is in {@code o} (tasks are never leaves).</li>
     * </ul>
     * Objects may be isolated and may have any number of predecessors.
     * <p>
     * Implementation: bitmask enumeration. For each {@code (t, o)} pair, each
     * task independently picks a pair {@code (P, S)} of disjoint non-empty
     * subsets of {@code o}; the induced task-to-task relation
     * {@code u -> v iff S(u) intersect P(v) is non-empty} is then checked for
     * acyclicity via DFS over bitmask adjacency.
     */
    public static Value DDGraphOf(final Value t, final Value o) throws Exception {
        Value tEnum = t.toSetEnum();
        Value oEnum = o.toSetEnum();
        if (!(tEnum instanceof SetEnumValue)) {
            throw new Exception("Task ids must be a set; got " + t.getClass().getName());
        }
        if (!(oEnum instanceof SetEnumValue)) {
            throw new Exception("Object ids must be a set; got " + o.getClass().getName());
        }
        Value[] allTasks = ((SetEnumValue) tEnum).elems.toArray();
        Value[] allObjects = ((SetEnumValue) oEnum).elems.toArray();

        if (allTasks.length > 30 || allObjects.length > 30) {
            throw new Exception("DDGraphOf: bitmask enumeration is limited to 30 task/object ids");
        }

        LOGGER.log(Level.FINE, "DDGraphOf: |T|={0}, |O|={1}",
                new Object[]{allTasks.length, allObjects.length});

        List<Value> results = new ArrayList<>();

        for (int tMask = 0; tMask < (1 << allTasks.length); tMask++) {
            Value[] tasks = pick(allTasks, tMask);
            for (int oMask = 0; oMask < (1 << allObjects.length); oMask++) {
                Value[] objects = pick(allObjects, oMask);
                enumerate(tasks, objects, results);
            }
        }

        LOGGER.log(Level.FINE, "DDGraphOf: produced {0} graphs", results.size());
        return new SetEnumValue(results.toArray(new Value[0]), false);
    }

    /**
     * Enumerate every DDGraph over the given task / object subsets and append
     * the resulting {@link RecordValue}s to {@code out}.
     */
    private static void enumerate(Value[] tasks, Value[] objects, List<Value> out) {
        if (tasks.length == 0) {
            out.add(emptyEdgeRecord(objects));
            return;
        }
        if (objects.length == 0) {
            return; // tasks would be isolated roots/leaves, violating the spec
        }

        long[][] options = new long[tasks.length][];
        for (int i = 0; i < tasks.length; i++) {
            options[i] = predSuccOptions(objects, tasks[i]);
            if (options[i].length == 0) {
                return; // some task has no valid (P, S) — no graph in this (t, o) cell
            }
        }

        int[] indices = new int[tasks.length];
        int[][] ps = new int[tasks.length][2];
        while (true) {
            for (int i = 0; i < tasks.length; i++) {
                long packed = options[i][indices[i]];
                ps[i][0] = (int) (packed >>> 32);
                ps[i][1] = (int) packed;
            }
            if (taskGraphIsAcyclic(ps)) {
                out.add(record(tasks, objects, ps));
            }
            if (!advance(indices, options)) {
                break;
            }
        }
    }

    // (P, S) options for a task, packed as ((long) P << 32) | S. Bit k of P
    // (resp. S) means objects[k] is a predecessor (resp. successor) of the
    // task. P and S are disjoint, both non-empty, and never include the task
    // itself (the last clause only matters when T and O overlap).
    private static long[] predSuccOptions(Value[] objects, Value task) {
        int n = objects.length;
        int forbid = 0;
        for (int i = 0; i < n; i++) {
            if (objects[i].equals(task)) {
                forbid |= 1 << i;
            }
        }
        int allowed = ((1 << n) - 1) & ~forbid;
        List<Long> opts = new ArrayList<>();
        // Iterate over every non-empty P subset of `allowed`.
        for (int p = allowed; p > 0; p = (p - 1) & allowed) {
            int rest = allowed & ~p;
            // Iterate over every non-empty S subset of `rest`.
            for (int s = rest; s > 0; s = (s - 1) & rest) {
                opts.add(((long) p << 32) | (s & 0xFFFFFFFFL));
            }
        }
        long[] out = new long[opts.size()];
        for (int i = 0; i < opts.size(); i++) {
            out[i] = opts.get(i);
        }
        return out;
    }

    /**
     * The bipartite graph is a DAG iff the induced task-to-task relation
     * {@code u_i -> u_j iff S(u_i) \cap P(u_j) != \emptyset} is acyclic.
     */
    private static boolean taskGraphIsAcyclic(int[][] ps) {
        int n = ps.length;
        int[] adj = new int[n];
        for (int i = 0; i < n; i++) {
            int si = ps[i][1];
            for (int j = 0; j < n; j++) {
                if (i == j) continue;
                if ((si & ps[j][0]) != 0) {
                    adj[i] |= 1 << j;
                }
            }
        }
        byte[] color = new byte[n]; // 0 = white, 1 = gray, 2 = black
        for (int i = 0; i < n; i++) {
            if (color[i] == 0 && hasCycle(i, adj, color)) {
                return false;
            }
        }
        return true;
    }

    private static boolean hasCycle(int v, int[] adj, byte[] color) {
        color[v] = 1;
        int bits = adj[v];
        while (bits != 0) {
            int w = Integer.numberOfTrailingZeros(bits);
            if (color[w] == 1) return true;
            if (color[w] == 0 && hasCycle(w, adj, color)) return true;
            bits &= bits - 1;
        }
        color[v] = 2;
        return false;
    }

    private static boolean advance(int[] indices, long[][] options) {
        for (int k = indices.length - 1; k >= 0; k--) {
            if (++indices[k] < options[k].length) {
                return true;
            }
            indices[k] = 0;
        }
        return false;
    }

    private static Value[] pick(Value[] all, int mask) {
        int n = Integer.bitCount(mask);
        Value[] out = new Value[n];
        int j = 0;
        int bits = mask;
        while (bits != 0) {
            int i = Integer.numberOfTrailingZeros(bits);
            out[j++] = all[i];
            bits &= bits - 1;
        }
        return out;
    }

    /** Build the record for an edge-less object-only graph. */
    private static RecordValue emptyEdgeRecord(Value[] objects) {
        Value nodeSet = new SetEnumValue(objects.clone(), false);
        Value edgeSet = new SetEnumValue(new Value[0], false);
        return makeRecord(nodeSet, edgeSet);
    }

    /** Build the record for a (t, o) graph given the per-task (P, S) selection. */
    private static RecordValue record(Value[] tasks, Value[] objects, int[][] ps) {
        Set<Value> nodes = new LinkedHashSet<>(Arrays.asList(tasks));
        nodes.addAll(Arrays.asList(objects));
        Value nodeSet = new SetEnumValue(nodes.toArray(new Value[0]), false);

        List<TupleValue> edges = new ArrayList<>();
        for (int i = 0; i < tasks.length; i++) {
            int p = ps[i][0];
            int s = ps[i][1];
            while (p != 0) {
                int k = Integer.numberOfTrailingZeros(p);
                edges.add(new TupleValue(objects[k], tasks[i]));
                p &= p - 1;
            }
            while (s != 0) {
                int k = Integer.numberOfTrailingZeros(s);
                edges.add(new TupleValue(tasks[i], objects[k]));
                s &= s - 1;
            }
        }
        Value edgeSet = new SetEnumValue(edges.toArray(new Value[0]), false);
        return makeRecord(nodeSet, edgeSet);
    }
}
