package visitor;

import ast.Node;

public interface StringVisitor extends Visitor {

    default Object visitChildren(Node node) {
        return node.accept(this);
    }
}
