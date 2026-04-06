 python:3.11-slim
WORKDIR /app
RUN pip install --no-cache-dir websocket-client
COPY main.py .
EXPOSE 8080
CMD ["python3", "-u", "main.py"]
