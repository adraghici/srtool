package tool;

import java.util.*;

public class Scopes {
    private final IdMap idMap;
    private final Stack<Map<String, Integer>> scopes;

    /**
     * This will enter a default scope when created.
     */
    public Scopes() {
        idMap = new IdMap();
        scopes = new Stack<>();
        scopes.push(new HashMap<>());
    }

    public void enterScope() {
        // System.out.println("PUSH()");
        scopes.add(new HashMap<>(scopes.peek()));
    }

    public void exitScope() {
        // System.out.println("POP()");
        scopes.pop();
        // for (Map.Entry entry : scopes.peek().entrySet()) {
        //     System.out.println("==>>> " + entry.getKey() + " : " + entry.getValue());
        // }

    }

    public void declareVar(String var) {
        scopes.peek().put(var, idMap.fresh(var));
    }

    public String getVar(String var) {
        return var + scopes.peek().get(var);
    }
}
