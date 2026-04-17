FROM python:3.11-slim
WORKDIR /app
COPY requirements.txt .
RUN pip install --no-cache-dir --root-user-action=ignore -r requirements.txt
COPY main.py .
EXPOSE 8080
CMD ["python3", "-u", "main.py"]
