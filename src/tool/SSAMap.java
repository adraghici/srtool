package tool;

import java.util.HashMap;
import java.util.Map;

/**
 * Created by costica1234 on 18/10/15.
 */
public class SSAMap {

    private Map<String, Integer> nextIDMap;
    private final int DEFAULT_ID = 0;

    public SSAMap() {
        nextIDMap = new HashMap<>();
    }

    public Integer getNextID(String var) {
        return nextIDMap.get(var);
    }

    public void assignVariable(String var) {
        if (nextIDMap.containsKey(var)) {
            Integer nextID = nextIDMap.get(var) + 1;
            nextIDMap.replace(var, nextID);
        } else {
            nextIDMap.put(var, DEFAULT_ID);
        }
    }

}
