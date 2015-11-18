package tool;

import ast.AssertStmt;
import ast.Node;
import ast.TraceableNode;
import ast.TraceableNode.SourceType;
import com.google.common.collect.Maps;

import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

public class CandidateAssertCollector {
    private final Map<AssertStmt, TraceableNode> assertOrigin;

    public CandidateAssertCollector() {
        assertOrigin = Maps.newHashMap();
    }

    public void add(TraceableNode parent, AssertStmt stmt) {
        while (parent.getSource().isPresent() && parent.getSourceType() != SourceType.REMOVING) {
            parent = parent.getSource().get();
        }
        assertOrigin.put(stmt.getOriginal() == null ? stmt : stmt.getOriginal(), parent);
    }

    public List<Node> resolve(List<AssertStmt> stmts) {
        return stmts.stream()
            .filter(stmt -> assertOrigin.containsKey(stmt.getOriginal()))
            .map(stmt -> assertOrigin.get(stmt.getOriginal()))
            .collect(Collectors.toList());
    }

    public List<AssertStmt> filterNonCandidate(List<AssertStmt> stmts) {
        return stmts.stream()
            .filter(stmt -> !assertOrigin.containsKey(stmt.getOriginal()))
            .collect(Collectors.toList());
    }

    public void clear() {
        assertOrigin.clear();
    }
}
