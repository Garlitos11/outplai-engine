# OutplAI Engine (web)

1. Upload these files to a GitHub repository: `outplai_web.py`, `requirements.txt`, `render.yaml`, `README.md`.
   (Optional: add `image_3c998c.png` next to `outplai_web.py` to use your logo.)
2. On render.com: New -> Blueprint (or Web Service) -> connect the repository -> free plan.
   Web Service settings if not using the blueprint:
   - Build command: `pip install -r requirements.txt`
   - Start command: `gunicorn outplai_web:application --threads 8 --timeout 120 --bind 0.0.0.0:$PORT`
3. Add the environment variable `ODDS_API_KEY` with your The Odds API key.
4. Keep it awake: create a free monitor at uptimerobot.com that requests your Render URL every 5 minutes.

Run locally: `python outplai_web.py`
