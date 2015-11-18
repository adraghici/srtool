package ast;

import visitor.VisitStage;

import java.util.Optional;

public interface TraceableNode extends Node {

    Optional<? extends TraceableNode> getSource();

    VisitStage getVisitStage();
}
