package tool;

import ast.AssertStmt;
import ast.Node;
import ast.TraceableNode;
import visitor.VisitStage;
import com.google.common.collect.Maps;

import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

/**
 * Collector used to aggregate assert statements and trace back to the point where they were originally
 * created.
 */
public class AssertCollector {
    private final Map<AssertStmt, TraceableNode> assertOrigin;

    public AssertCollector() {
        assertOrigin = Maps.newHashMap();
    }

    public void add(TraceableNode parent, AssertStmt stmt) {
        TraceableNode cleanAncestor = getCleanAncestor(parent);
        assertOrigin.put(stmt, cleanAncestor);
    }

    public List<Node> resolve(List<AssertStmt> stmts) {
        return stmts.stream()
            .filter(stmt -> assertOrigin.containsKey(stmt.getOriginal()))
            .map(stmt -> assertOrigin.get(stmt.getOriginal()))
            .collect(Collectors.toList());
    }

    public boolean containsAll(List<AssertStmt> stmts) {
        return stmts.stream().noneMatch(stmt -> !assertOrigin.containsKey(stmt.getOriginal()));
    }

    public void clear() {
        assertOrigin.clear();
    }

    private static TraceableNode getCleanAncestor(TraceableNode node) {
        TraceableNode parent = node;
        while (parent.getSource().isPresent() && parent.getVisitStage() != VisitStage.CLEAN) {
            parent = parent.getSource().get();
        }
        return parent;
    }
}
