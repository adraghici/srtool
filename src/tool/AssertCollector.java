package tool;

import ast.AssertStmt;
import ast.Node;
import com.google.common.collect.BiMap;
import com.google.common.collect.HashBiMap;
import com.google.common.collect.Sets;

import java.util.List;
import java.util.Set;

/**
 * Collector used to aggregate statements and trace back to the point where they were originally created.
 */
public class AssertCollector {
    private final Set<Node> visited;
    private final BiMap<Node, Node> origin;

    public AssertCollector() {
        visited = Sets.newHashSet();
        origin = HashBiMap.create();
    }

    public void add(Node parent, AssertStmt stmt) {
        if (!visited.contains(parent)) {
            return;
        }

        origin.put(stmt, origin.get(parent));
    }

    public List<Node> resolve(List<AssertStmt> stmts) {
        // TODO
        return null;
    }

    public boolean containsAny(List<AssertStmt> stmts) {
        return stmts.stream().anyMatch(this::contains);
    }

    public boolean containsAll(List<AssertStmt> stmts) {
        return stmts.stream().allMatch(this::contains);
    }

    public void clear() {
        origin.clear();
    }

    private boolean contains(AssertStmt stmt) {
        return origin.containsKey(stmt);
    }
}
