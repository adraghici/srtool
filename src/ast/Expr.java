package ast;

import java.util.Map;

public interface Expr extends Node {
    Expr replace(Map<String, Expr> vars);
}
