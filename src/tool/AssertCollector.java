package tool;

import ast.AssertStmt;
import ast.Node;
import ast.TraceableNode;
import ast.TraceableNode.SourceType;
import com.google.common.collect.BiMap;
import com.google.common.collect.HashBiMap;

import java.util.List;
import java.util.stream.Collectors;

public class AssertCollector {
    private final BiMap<TraceableNode, AssertStmt> assertOrigin;

    public AssertCollector() {
        assertOrigin = HashBiMap.create();
    }

    public void add(TraceableNode source, AssertStmt assertStmt) {
        while (source.getSource().isPresent() && (source.getSourceType() == SourceType.SHADOWING)) {
            source = source.getSource().get();
        }
        assertOrigin.put(source, assertStmt);
    }

    public List<Node> resolve(List<AssertStmt> assertStmts) {
        return assertStmts.stream()
            .map(stmt -> assertOrigin.inverse().get(stmt))
            .collect(Collectors.toList());
    }

    public void clear() {
        assertOrigin.clear();
    }
}
