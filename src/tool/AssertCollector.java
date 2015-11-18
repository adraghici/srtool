package tool;

import ast.AssertStmt;
import ast.Node;
import ast.TraceableNode;
import com.google.common.collect.Maps;
import visitor.VisitStage;

import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.stream.Collectors;

/**
 * Collector used to aggregate assert statements and trace back to the point where they were originally
 * created.
 */
public class AssertCollector {
    private final Map<AssertStmt, Optional<TraceableNode>> assertOrigin;

    public AssertCollector() {
        assertOrigin = Maps.newHashMap();
    }

    public void add(Optional<TraceableNode> parent, AssertStmt stmt) {
        assertOrigin.put(stmt, parent.map(AssertCollector::getCleanAncestor));
    }

    public List<Node> resolve(List<AssertStmt> stmts) {
        return stmts.stream()
            .filter(stmt -> assertOrigin.containsKey(stmt.getOriginal()))
            .map(stmt -> assertOrigin.get(stmt.getOriginal()).get())
            .collect(Collectors.toList());
    }

    public boolean containsAny(List<AssertStmt> stmts) {
        return stmts.stream().anyMatch(this::contains);
    }

    public boolean containsAll(List<AssertStmt> stmts) {
        return stmts.stream().allMatch(this::contains);
    }

    public void clear() {
        assertOrigin.clear();
    }

    private boolean contains(AssertStmt stmt) {
        return assertOrigin.containsKey(stmt.getOriginal());
    }

    private static TraceableNode getCleanAncestor(TraceableNode node) {
        TraceableNode parent = node;
        while (parent.getSource().isPresent() && parent.getVisitStage() != VisitStage.CLEAN) {
            parent = parent.getSource().get();
        }
        return parent;
    }
}
