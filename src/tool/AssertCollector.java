package tool;

import ast.AssertStmt;
import ast.Node;
import com.google.common.collect.Maps;
import com.google.common.collect.Sets;

import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * Collector used to aggregate assert statements and trace back to the point where they were originally
 * created.
 */
public class AssertCollector {
    private final Set<Node> visited;
    private final Map<Node, Node> origin;

    public AssertCollector() {
        visited = Sets.newHashSet();
        origin = Maps.newHashMap();
    }

    public void addOrigin(Node node) {
        origin.put(node, node);
        visited.add(node);
    }

    public void add(Node parent, Node node) {
        if (visited.contains(parent)) {
            origin.put(node, origin.get(parent));
            visited.add(node);
        }
    }

    public List<Node> resolve(List<AssertStmt> stmts) {
        return stmts.stream().filter(origin::containsKey).map(origin::get).collect(Collectors.toList());
    }

    public void clear() {
        visited.clear();
        origin.clear();
    }
}
