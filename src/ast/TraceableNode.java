package ast;

import java.util.Optional;

public interface TraceableNode extends Node {
    enum SourceType { UNKNOWN, SHADOWING, CALL, WHILE, RETURN, REMOVING }

    Optional<? extends TraceableNode> getSource();

    SourceType getSourceType();
}
