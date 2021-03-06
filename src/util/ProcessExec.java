package util;
import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.util.concurrent.TimeoutException;

public class ProcessExec {
	private static int INITIAL_BUFFER_LENGTH = 2048;

	private final ProcessBuilder processBuilder;
	public String stdout = null;
	public String stderr = null;
	
	public ProcessExec(String ... command)
	{
		processBuilder = new ProcessBuilder(command);
	}
	
	/**
	 * Executes the command.
	 * Pipes the String "stdin" to the process.
	 * Waits for "timeout" seconds for the process to terminate.
	 * After calling this method, the fields "stdout" and "stderr"
	 * contain the contents of the stdout and stderr of the process.
	 * The stdout is also returned.
	 * 
	 * @param stdin Piped to the process.
	 * @param timeout Time to wait in milliseconds.
	 * @return The stdout of the process. 
	 * @throws TimeoutException If timeout occurs.
	 * @throws IOException
	 * @throws InterruptedException
	 */
	public String execute(String stdin, long timeout) throws IOException, TimeoutException, InterruptedException {
		stdout = null;
		stderr = null;
		
		Thread thread1=null;
		Thread thread2=null;
		Thread thread3=null;
		Process process = processBuilder.start();
		
		ByteArrayOutputStream stdoutStream = new ByteArrayOutputStream(INITIAL_BUFFER_LENGTH);
		ByteArrayOutputStream stderrStream = new ByteArrayOutputStream(INITIAL_BUFFER_LENGTH);
		ByteArrayInputStream stdinStream = new ByteArrayInputStream(stdin.getBytes());
		
		thread1 = FileUtil.copy(process.getInputStream(), stdoutStream);
		thread2 = FileUtil.copy(process.getErrorStream(), stderrStream);
		thread3 = FileUtil.copy(stdinStream, process.getOutputStream());
		
		Worker worker = new Worker(process);
		worker.start();
		boolean timedout = false;
		try {
			worker.join(timeout);
			if(worker.exit == null)
			{
				timedout = true;
			}
		} catch (InterruptedException ex) {
			worker.interrupt();
			Thread.currentThread().interrupt();
			timedout = true;
			throw ex;
		} finally {
			if(timedout)
			{
				process.destroy();
			}
		}
		
		worker.join();
		
		thread1.join();
		thread2.join();
		thread3.join();
		
		if(timedout)
		{
			throw new TimeoutException("SMT solver timeout.");
		}
		stdout = stdoutStream.toString();
		stderr = stderrStream.toString();
		return stdout;
	}
	
	private static class Worker extends Thread {
		  private final Process process;
		  public volatile Integer exit;
		  private Worker(Process process) {
		    this.process = process;
		  }
		  public void run() {
		    try { 
		      exit = process.waitFor();
		    } catch (InterruptedException ignore) {
		      return;
		    }
		  }  
		}
	
}
